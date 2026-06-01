#!/bin/bash

# Ralph Loop Runner with Inline Dashboard
# Usage: ./ralph.sh [PROMPT_FILE] [--agent claude|codex]
# Default prompt: projects/typedtree-parity/RALPH_PROMPT.md
# Default agent: claude (or RALPH_AGENT env var)
# Output logs: per-run files in RALPH_OUTPUT_DIR, TMPDIR, or /tmp

PROMPT_FILE="projects/typedtree-parity/RALPH_PROMPT.md"
AGENT="${RALPH_AGENT:-claude}"
OUTPUT_FILE=""
OUTPUT_JSON_FILE=""
ITERATION=0
CODEX_LAST_TEXT=""
CODEX_MCP_UNREACHABLE_REPORTED=0
DEFAULT_SLEEP_SECONDS=2
RATE_LIMIT_BASE_SLEEP_SECONDS=60
RATE_LIMIT_MAX_SLEEP_SECONDS=900
RATE_LIMIT_STREAK=0

usage() {
  cat <<'USAGE'
Usage: ./ralph.sh [PROMPT_FILE] [--agent claude|codex]

Examples:
  ./ralph.sh
  ./ralph.sh projects/typedtree-parity/RALPH_PROMPT.md
  ./ralph.sh projects/typedtree-parity/RALPH_PROMPT.md --agent codex
  RALPH_AGENT=codex ./ralph.sh projects/typedtree-parity/RALPH_PROMPT.md
USAGE
}

PROMPT_SET=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --agent)
      if [[ -z "${2:-}" ]]; then
        echo "Error: --agent requires a value (claude or codex)"
        exit 1
      fi
      AGENT="$2"
      shift 2
      ;;
    --agent=*)
      AGENT="${1#*=}"
      shift
      ;;
    *)
      if [[ $PROMPT_SET -eq 1 ]]; then
        echo "Error: Unexpected argument '$1'"
        usage
        exit 1
      fi
      PROMPT_FILE="$1"
      PROMPT_SET=1
      shift
      ;;
  esac
done

case "$AGENT" in
  claude)
    AGENT_DISPLAY="Claude Code"
    ;;
  codex)
    AGENT_DISPLAY="Codex"
    ;;
  *)
    echo "Error: Unsupported agent '$AGENT'. Use 'claude' or 'codex'."
    exit 1
    ;;
esac

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "Error: Prompt file '$PROMPT_FILE' not found"
  exit 1
fi

if [[ "$AGENT" == "claude" ]]; then
  if ! command -v claude >/dev/null 2>&1; then
    echo "Error: 'claude' command not found in PATH"
    exit 1
  fi
else
  if ! command -v codex >/dev/null 2>&1; then
    echo "Error: 'codex' command not found in PATH"
    exit 1
  fi
  if ! command -v jq >/dev/null 2>&1; then
    echo "Error: 'jq' is required for --agent codex"
    exit 1
  fi
fi

# Derive project directory from prompt file location
PROJECT_DIR="$(dirname "$PROMPT_FILE")"
TODO_FILE="$PROJECT_DIR/RALPH_TODO.md"

init_output_files() {
  local output_dir="${RALPH_OUTPUT_DIR:-${TMPDIR:-/tmp}}"

  if [[ ! -d "$output_dir" ]]; then
    echo "Error: Output directory '$output_dir' not found"
    exit 1
  fi

  OUTPUT_FILE="$(mktemp "${output_dir%/}/ralph_output.XXXXXX")" || exit 1
  OUTPUT_JSON_FILE="$(mktemp "${output_dir%/}/ralph_output_json.XXXXXX")" || exit 1
}

build_prompt_input() {
  {
    echo "**Project directory:** \`$PROJECT_DIR/\` — All relative file references in this prompt (e.g. \`RALPH_TODO.md\`) are relative to this directory."
    echo ""
    cat "$PROMPT_FILE"
  }
}

is_control_token_emitted() {
  local token="$1"
  if [[ ! -f "$OUTPUT_FILE" ]]; then
    return 1
  fi

  grep -Eq "^[[:space:]]*${token}[[:space:]]*$" "$OUTPUT_FILE"
}

project_requires_typedtree_parity_gate() {
  [[ "$PROJECT_DIR" == *"typedtree-parity"* ]]
}

verify_typedtree_full_parity() {
  local parity_output
  local clean_output
  local total
  local rust_pass
  local rust_fail
  local parity_pass
  local parity_fail

  echo ""
  echo "🔎 Verifying typedtree parity before accepting RALPH_COMPLETE..."

  if ! parity_output=$(timeout 600 ./scripts/test_typedtree_parity.sh --with-locs --parallel 1 2>&1); then
    echo "Typedtree parity gate failed to run cleanly; completion denied."
    echo "$parity_output" | tail -40
    return 1
  fi

  clean_output=$(printf '%s\n' "$parity_output" | sed -E $'s/\x1B\\[[0-9;]*[mK]//g')
  read -r rust_pass rust_fail <<<"$(printf '%s\n' "$clean_output" | sed -nE 's/^Rust bsc:[[:space:]]*([0-9]+) passed,[[:space:]]*([0-9]+) failed$/\1 \2/p' | tail -1)"
  read -r parity_pass parity_fail <<<"$(printf '%s\n' "$clean_output" | sed -nE 's/^Parity:[[:space:]]*([0-9]+) passed,[[:space:]]*([0-9]+) failed$/\1 \2/p' | tail -1)"
  if [[ -n "$rust_pass" && -n "$rust_fail" ]]; then
    total=$((rust_pass + rust_fail))
  fi

  if [[ -z "$total" || -z "$rust_pass" || -z "$rust_fail" || -z "$parity_pass" || -z "$parity_fail" ]]; then
    echo "Typedtree parity gate could not parse summary output; completion denied."
    echo "$clean_output" | tail -40
    return 1
  fi

  if [[ $((parity_pass + parity_fail)) -ne "$total" ]]; then
    echo "Typedtree parity gate found inconsistent totals; completion denied."
    echo "$clean_output" | tail -40
    return 1
  fi

  echo "Typedtree parity summary: Rust ${rust_pass}/${total} (fail ${rust_fail}), Parity ${parity_pass}/${total} (fail ${parity_fail})"

  if [[ "$rust_fail" -eq 0 && "$parity_fail" -eq 0 && "$rust_pass" -eq "$total" && "$parity_pass" -eq "$total" ]]; then
    return 0
  fi

  echo "Typedtree parity is below 100%; ignoring RALPH_COMPLETE and continuing."
  return 1
}

render_claude_stream_line() {
  local line="$1"

  # Parse stream-json and extract content
  if echo "$line" | grep -q '"type":"assistant"'; then
    # Extract text from assistant messages
    TEXT=$(echo "$line" | grep -o '"text":"[^"]*"' | sed 's/"text":"//;s/"$//' | sed 's/\\n/\n/g')
    if [[ -n "$TEXT" ]]; then
      echo -e "$TEXT"
    fi
  elif echo "$line" | grep -q '"tool_use"'; then
    # Show tool usage
    TOOL=$(echo "$line" | grep -o '"name":"[^"]*"' | head -1 | sed 's/"name":"//;s/"$//')
    if [[ -n "$TOOL" ]]; then
      echo "  ⚡ $TOOL"
    fi
  elif echo "$line" | grep -q '"tool_result"'; then
    echo "  ✓ done"
  fi
}

render_codex_stream_line() {
  local line="$1"
  local text
  local tool_start
  local tool_done
  local tool_name
  local tool_id
  local tool_meta
  local tool_status
  local tool_exit

  if [[ "$line" != \{* ]]; then
    if echo "$line" | grep -q "rmcp::transport::worker: worker quit with fatal: Transport channel closed" && \
       echo "$line" | grep -q "127.0.0.1:3845"; then
      if [[ $CODEX_MCP_UNREACHABLE_REPORTED -eq 0 ]]; then
        echo "  ! Codex MCP server not reachable at 127.0.0.1:3845; continuing without MCP."
        CODEX_MCP_UNREACHABLE_REPORTED=1
      fi
      return
    fi

    if echo "$line" | grep -Eiq "error|warning|failed|fatal"; then
      echo "$line"
    fi
    return
  fi

  text=$(echo "$line" | jq -r '
    def assistant_text:
      if .type == "agent_message" then
        (.message // .text // empty)
      elif .type == "response_item" and .payload.type == "message" and .payload.role == "assistant" then
        ([.payload.content[]? | select(.type == "output_text") | .text] | join("\n"))
      elif .type == "message" and .role == "assistant" then
        ([.content[]? | select(.type == "output_text") | .text] | join("\n"))
      elif .type == "output_text" then
        (.text // empty)
      else
        empty
      end;
    [
      assistant_text,
      (.payload? | assistant_text),
      (.item? | assistant_text),
      (.payload?.item? | assistant_text)
    ]
    | map(select(. != null and . != ""))
    | .[0] // empty
  ' 2>/dev/null)
  if [[ -n "$text" && "$text" != "null" ]]; then
    if [[ "$text" != "$CODEX_LAST_TEXT" ]]; then
      echo -e "$text"
      CODEX_LAST_TEXT="$text"
    fi
  fi

  tool_start=$(echo "$line" | jq -r '
    def started_tool:
      if .type == "item.started" and .item.type == "command_execution" then
        ["command_execution", (.item.id // ""), (.item.command // "")]
      elif .type == "response_item" and .payload.type == "function_call" then
        [(.payload.name // "function_call"), (.payload.call_id // ""), (.payload.arguments // "")]
      elif .type == "function_call" then
        [(.name // "function_call"), (.call_id // ""), (.arguments // "")]
      else
        empty
      end;
    [started_tool, (.payload? | started_tool)]
    | map(select(. != null and . != ""))
    | .[0]
    | if . == null then
        empty
      else
        .[2] |= (gsub("\\s+"; " ") | .[0:140]) | @tsv
      end
  ' 2>/dev/null)
  if [[ -n "$tool_start" && "$tool_start" != "null" ]]; then
    IFS=$'\t' read -r tool_name tool_id tool_meta <<<"$tool_start"
    if [[ -n "$tool_id" && -n "$tool_meta" ]]; then
      echo "  ⚡ $tool_name [$tool_id] $tool_meta"
    elif [[ -n "$tool_id" ]]; then
      echo "  ⚡ $tool_name [$tool_id]"
    else
      echo "  ⚡ $tool_name"
    fi
  fi

  tool_done=$(echo "$line" | jq -r '
    def completed_tool:
      if .type == "item.completed" and .item.type == "command_execution" then
        ["command_execution", (.item.id // ""), (.item.status // ""), ((.item.exit_code // "") | tostring)]
      elif .type == "response_item" and .payload.type == "function_call_output" then
        ["function_call_output", (.payload.call_id // ""), "", ""]
      elif .type == "function_call_output" then
        ["function_call_output", (.call_id // ""), "", ""]
      else
        empty
      end;
    [completed_tool, (.payload? | completed_tool)]
    | map(select(. != null and . != ""))
    | .[0]
    | if . == null then empty else @tsv end
  ' 2>/dev/null)
  if [[ -n "$tool_done" && "$tool_done" != "null" ]]; then
    IFS=$'\t' read -r tool_name tool_id tool_status tool_exit <<<"$tool_done"
    if [[ "$tool_name" == "command_execution" ]]; then
      if [[ "$tool_status" == "completed" && "$tool_exit" == "0" ]]; then
        echo "  ✓ $tool_name [$tool_id] exit $tool_exit"
      elif [[ -n "$tool_exit" ]]; then
        echo "  ✗ $tool_name [$tool_id] status ${tool_status:-unknown} exit $tool_exit"
      else
        echo "  ✗ $tool_name [$tool_id] status ${tool_status:-unknown}"
      fi
    elif [[ -n "$tool_id" ]]; then
      echo "  ✓ $tool_name [$tool_id]"
    else
      echo "  ✓ $tool_name"
    fi
  fi
}

run_agent_iteration() {
  if [[ "$AGENT" == "claude" ]]; then
    build_prompt_input | \
      claude --dangerously-skip-permissions --print --output-format stream-json --verbose 2>&1 | \
      tee "$OUTPUT_JSON_FILE" | \
      while IFS= read -r line; do
        render_claude_stream_line "$line"
      done | tee "$OUTPUT_FILE"
  else
    CODEX_LAST_TEXT=""
    CODEX_MCP_UNREACHABLE_REPORTED=0
    build_prompt_input | \
      codex exec --dangerously-bypass-approvals-and-sandbox --json - 2>&1 | \
      tee "$OUTPUT_JSON_FILE" | \
      while IFS= read -r line; do
        render_codex_stream_line "$line"
      done | tee "$OUTPUT_FILE"
  fi
}

# Function to show inline dashboard
show_dashboard() {
  # Get TODO progress
  if [[ -f $TODO_FILE ]]; then
    TOTAL=$(grep -c "^\- \[" $TODO_FILE 2>/dev/null) || TOTAL=0
    DONE=$(grep -c "^\- \[[x~]\]" $TODO_FILE 2>/dev/null) || DONE=0
    TOTAL=${TOTAL:-0}
    DONE=${DONE:-0}
    REMAINING=$((TOTAL - DONE))
    if [[ $TOTAL -gt 0 ]]; then
      PERCENT=$((DONE * 100 / TOTAL))
      FILLED=$((DONE * 20 / TOTAL))
    else
      PERCENT=0
      FILLED=0
    fi
    EMPTY=$((20 - FILLED))

    # Progress bar
    BAR=""
    for ((i=0; i<FILLED; i++)); do BAR+="█"; done
    for ((i=0; i<EMPTY; i++)); do BAR+="░"; done

    echo "┌────────────────────────────────────────────────────────────────────┐"
    printf "│ Progress: %d/%d (%d%%) [%s] │\n" "$DONE" "$TOTAL" "$PERCENT" "$BAR"

    # Next task
    NEXT_TASK=$(grep "^\- \[ \]" $TODO_FILE | head -1 | sed 's/^- \[ \] //' | cut -c1-50)
    if [[ -n "$NEXT_TASK" ]]; then
      printf "│ Next: %-60s │\n" "$NEXT_TASK"
    fi

    # Recent commits (last 2)
    COMMITS=$(git log --oneline -2 2>/dev/null | tr '\n' ' ' | cut -c1-60)
    if [[ -n "$COMMITS" ]]; then
      printf "│ Commits: %-57s │\n" "$COMMITS"
    fi

    echo "└────────────────────────────────────────────────────────────────────┘"
  fi
}

has_control_token() {
  local token="$1"
  grep -Eq "^[[:space:]]*${token}[[:space:]]*$" "$OUTPUT_FILE"
}

init_output_files

clear
echo "╔══════════════════════════════════════════════════════════════════════╗"
echo "║                         RALPH LOOP                                   ║"
echo "║  Prompt: $(printf '%-58s' "$PROMPT_FILE")  ║"
echo "║  Project: $(printf '%-57s' "$PROJECT_DIR/") ║"
echo "║  Agent: $(printf '%-59s' "$AGENT_DISPLAY") ║"
echo "║  Text log: $(printf '%-56s' "$OUTPUT_FILE") ║"
echo "║  JSON log: $(printf '%-56s' "$OUTPUT_JSON_FILE") ║"
echo "║  Press Ctrl+C to stop                                                ║"
echo "╚══════════════════════════════════════════════════════════════════════╝"
echo ""

while true; do
  ITERATION=$((ITERATION + 1))

  echo ""
  echo "═══════════════════════════════════════════════════════════════════════"
  echo " Iteration $ITERATION - $(date '+%H:%M:%S')"
  echo "═══════════════════════════════════════════════════════════════════════"

  show_dashboard

  echo ""
  echo "─── $AGENT_DISPLAY Output ─────────────────────────────────────────────"
  echo ""

  # Run selected agent with streaming output for real-time visibility
  run_agent_iteration

  echo ""
  echo "─── End of Iteration $ITERATION ───────────────────────────────────────"

  # Check for completion
  if is_control_token_emitted "RALPH_COMPLETE"; then
    if project_requires_typedtree_parity_gate && ! verify_typedtree_full_parity; then
      RATE_LIMIT_STREAK=0
      sleep "$DEFAULT_SLEEP_SECONDS"
      continue
    fi
    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    echo "║  🎉 RALPH_COMPLETE - Finished after $ITERATION iterations!            ║"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    exit 0
  fi

  # Check for blocked state
  if is_control_token_emitted "RALPH_BLOCKED"; then
    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    echo "║  ⚠️  RALPH_BLOCKED - Needs human intervention                        ║"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    exit 1
  fi

  # Back off only on high-confidence limit errors to avoid false positives from
  # unrelated output (e.g. file line numbers like "429" or generic "rate limit" text).
  if grep -Eiq "you.?ve hit your limit|hit your limit|rate[_[:space:]-]?limit (reached|exceeded)|too many requests|quota exceeded|insufficient[_[:space:]-]?quota|status( code)?[[:space:]]*429|http[[:space:]]*429" "$OUTPUT_FILE" "$OUTPUT_JSON_FILE"; then
    RATE_LIMIT_STREAK=$((RATE_LIMIT_STREAK + 1))
    BACKOFF_SECONDS=$((RATE_LIMIT_BASE_SLEEP_SECONDS * (2 ** (RATE_LIMIT_STREAK - 1))))
    if [[ $BACKOFF_SECONDS -gt $RATE_LIMIT_MAX_SLEEP_SECONDS ]]; then
      BACKOFF_SECONDS=$RATE_LIMIT_MAX_SLEEP_SECONDS
    fi

    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    printf "║  ⏳ %-11s limit detected - sleeping %4ss (streak %2d)              ║\n" "$AGENT_DISPLAY" "$BACKOFF_SECONDS" "$RATE_LIMIT_STREAK"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    sleep "$BACKOFF_SECONDS"
    continue
  fi

  RATE_LIMIT_STREAK=0
  sleep "$DEFAULT_SLEEP_SECONDS"
done
