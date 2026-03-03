#!/usr/bin/env bash
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                // foundry // extension // icons
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Generate PNG icons from the Foundry SVG source.
# Uses rsvg-convert from librsvg (available in foundry dev shell).
#
# Usage: ./scripts/generate-icons.sh
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ICONS_DIR="$SCRIPT_DIR/../extension/icons"
SVG_SOURCE="$ICONS_DIR/foundry.svg"

echo ""
echo "  FOUNDRY // icon generation"
echo ""

# Check for rsvg-convert
if ! command -v rsvg-convert &>/dev/null; then
	echo "  ERROR: rsvg-convert not found"
	echo "  Run from foundry dev shell: nix develop"
	exit 1
fi

# Check SVG source exists
if [[ ! -f "$SVG_SOURCE" ]]; then
	echo "  ERROR: SVG source not found at $SVG_SOURCE"
	exit 1
fi

echo "  Source: $SVG_SOURCE"
echo "  Output: $ICONS_DIR"
echo ""

# Generate each size
for size in 16 48 128; do
	output="$ICONS_DIR/icon${size}.png"
	echo "  Generating icon${size}.png..."
	rsvg-convert -w "$size" -h "$size" "$SVG_SOURCE" -o "$output"
done

echo ""
echo "  Done! Generated:"
ls -la "$ICONS_DIR"/*.png 2>/dev/null || echo "  (no PNG files found)"
echo ""
