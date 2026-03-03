#!/usr/bin/env bash
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                             // foundry // extension // bundle
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Bundle the extraction modules into a single content script.
# Uses esbuild to combine ES6 modules into IIFE format for content scripts.
#
# Usage: ./scripts/bundle-extraction.sh
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXT_DIR="$SCRIPT_DIR/../extension"
INPUT="$EXT_DIR/extraction/index.js"
OUTPUT="$EXT_DIR/content-bundled.js"

echo ""
echo "  FOUNDRY // bundle extraction"
echo ""

# Check for esbuild
if ! command -v esbuild &>/dev/null; then
	echo "  ERROR: esbuild not found"
	echo "  Run from foundry dev shell or: nix-shell -p esbuild"
	exit 1
fi

# Check input exists
if [[ ! -f "$INPUT" ]]; then
	echo "  ERROR: Input not found at $INPUT"
	exit 1
fi

echo "  Input:  $INPUT"
echo "  Output: $OUTPUT"
echo ""

# Bundle with esbuild
# - IIFE format (immediately invoked function expression) for content script
# - No external dependencies (all code inlined)
# - Target modern browsers (ES2020)
esbuild "$INPUT" \
	--bundle \
	--format=iife \
	--target=es2020 \
	--outfile="$OUTPUT" \
	--minify=false

# Get file sizes
INPUT_LINES=$(find "$EXT_DIR/extraction" -name "*.js" -exec cat {} \; | wc -l)
OUTPUT_SIZE=$(stat -c%s "$OUTPUT" 2>/dev/null || stat -f%z "$OUTPUT")

echo ""
echo "  Done!"
echo "  Input:  ~$INPUT_LINES lines from extraction/*.js"
echo "  Output: $(echo "$OUTPUT_SIZE" | numfmt --to=iec 2>/dev/null || echo "$OUTPUT_SIZE bytes")"
echo ""
echo "  Update manifest.json to use: content-bundled.js"
echo ""
