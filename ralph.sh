#!/bin/bash

# Ralph Loop Runner with Inline Dashboard
# Usage: ./ralph.sh [PROMPT_FILE]
# Default: RALPH_PROMPT.md

PROMPT_FILE="${1:-RALPH_PROMPT.md}"
OUTPUT_FILE="/tmp/ralph_output.txt"
ITERATION=0
DEFAULT_SLEEP_SECONDS=2
RATE_LIMIT_BASE_SLEEP_SECONDS=60
RATE_LIMIT_MAX_SLEEP_SECONDS=900
RATE_LIMIT_STREAK=0

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "Error: Prompt file '$PROMPT_FILE' not found"
  exit 1
fi

# Derive project directory from prompt file location
PROJECT_DIR="$(dirname "$PROMPT_FILE")"
TODO_FILE="$PROJECT_DIR/RALPH_TODO.md"

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

clear
echo "╔══════════════════════════════════════════════════════════════════════╗"
echo "║                         RALPH LOOP                                   ║"
echo "║  Prompt: $(printf '%-58s' "$PROMPT_FILE")  ║"
echo "║  Project: $(printf '%-57s' "$PROJECT_DIR/") ║"
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
  echo "─── Claude Output ─────────────────────────────────────────────────────"
  echo ""

  # Run claude with streaming output for real-time visibility
  # Prepend project directory context so agent resolves relative paths correctly
  { echo "**Project directory:** \`$PROJECT_DIR/\` — All relative file references in this prompt (e.g. \`RALPH_TODO.md\`) are relative to this directory."; echo ""; cat "$PROMPT_FILE"; } | \
  claude --dangerously-skip-permissions --print --output-format stream-json --verbose 2>&1 | \
    tee "$OUTPUT_FILE.json" | \
    while IFS= read -r line; do
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
    done | tee "$OUTPUT_FILE"

  echo ""
  echo "─── End of Iteration $ITERATION ───────────────────────────────────────"

  # Check for completion
  if grep -q "RALPH_COMPLETE" "$OUTPUT_FILE"; then
    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    echo "║  🎉 RALPH_COMPLETE - Finished after $ITERATION iterations!            ║"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    exit 0
  fi

  # Check for blocked state
  if grep -q "RALPH_BLOCKED" "$OUTPUT_FILE"; then
    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    echo "║  ⚠️  RALPH_BLOCKED - Needs human intervention                        ║"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    exit 1
  fi

  # Back off when Claude reports account/request limits to avoid hammering the API.
  if grep -Eiq "you.?ve hit your limit|hit your limit|rate limit|too many requests|\\b429\\b" "$OUTPUT_FILE" "$OUTPUT_FILE.json"; then
    RATE_LIMIT_STREAK=$((RATE_LIMIT_STREAK + 1))
    BACKOFF_SECONDS=$((RATE_LIMIT_BASE_SLEEP_SECONDS * (2 ** (RATE_LIMIT_STREAK - 1))))
    if [[ $BACKOFF_SECONDS -gt $RATE_LIMIT_MAX_SLEEP_SECONDS ]]; then
      BACKOFF_SECONDS=$RATE_LIMIT_MAX_SLEEP_SECONDS
    fi

    echo ""
    echo "╔══════════════════════════════════════════════════════════════════════╗"
    printf "║  ⏳ Claude limit detected - sleeping %4ss (streak %2d)              ║\n" "$BACKOFF_SECONDS" "$RATE_LIMIT_STREAK"
    echo "╚══════════════════════════════════════════════════════════════════════╝"
    sleep "$BACKOFF_SECONDS"
    continue
  fi

  RATE_LIMIT_STREAK=0
  sleep "$DEFAULT_SLEEP_SECONDS"
done
