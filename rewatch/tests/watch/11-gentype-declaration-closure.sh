#!/bin/bash
set -euo pipefail
exec "$(dirname "$0")/../gentype/03-declaration-closure.sh" watch
