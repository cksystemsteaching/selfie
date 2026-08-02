#!/bin/sh
# Regenerate what-is-intelligence.pdf from index.html.
#
# The deck renders itself: index.html?print lays the slides out as a stack of
# 1600x900 pages with every build step shown and every figure drawn once at a
# fixed time, so the output is deterministic. All this script does is drive
# headless Chrome over that page. There is no build step and no dependency —
# the PDF is a rendering of the one file, not a separate artifact to maintain.
#
#   ./make-pdf.sh              light theme, the default for reading and printing
#   THEME=dark ./make-pdf.sh   the deck as it looks on a projector
#
# Kept in sync by .github/workflows/deck-pdf.yml, which reruns this whenever
# index.html changes on main and commits the result if it differs.

set -eu

cd "$(dirname "$0")"

OUT=what-is-intelligence.pdf
THEME=${THEME:-light}

CHROME=
for c in \
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
  "/Applications/Chromium.app/Contents/MacOS/Chromium" \
  "$(command -v google-chrome 2>/dev/null || true)" \
  "$(command -v google-chrome-stable 2>/dev/null || true)" \
  "$(command -v chromium 2>/dev/null || true)" \
  "$(command -v chromium-browser 2>/dev/null || true)"
do
  if [ -n "$c" ] && [ -x "$c" ]; then CHROME=$c; break; fi
done

if [ -z "$CHROME" ]; then
  echo "make-pdf: no Chrome or Chromium found" >&2
  exit 1
fi

PROFILE=$(mktemp -d)
CHROME_PID=
cleanup() {
  [ -n "$CHROME_PID" ] && kill "$CHROME_PID" 2>/dev/null
  rm -rf "$PROFILE"
}
trap cleanup EXIT

rm -f "$OUT"

"$CHROME" \
  --headless=new \
  --disable-gpu \
  --no-sandbox \
  --no-pdf-header-footer \
  --virtual-time-budget=30000 \
  --user-data-dir="$PROFILE" \
  --print-to-pdf="$OUT" \
  "file://$PWD/index.html?print&theme=$THEME" >/dev/null 2>&1 &
CHROME_PID=$!

# Chrome has been known to sit there after writing the file, so wait for the
# PDF to be complete rather than for the process to exit. %%EOF is the marker.
i=0
while [ "$i" -lt 180 ]; do
  if [ -s "$OUT" ] && LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then break; fi
  kill -0 "$CHROME_PID" 2>/dev/null || break
  sleep 1
  i=$((i + 1))
done

kill "$CHROME_PID" 2>/dev/null || true
wait "$CHROME_PID" 2>/dev/null || true
CHROME_PID=

if [ ! -s "$OUT" ] || ! LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then
  echo "make-pdf: Chrome produced no complete PDF" >&2
  exit 1
fi

# page objects, not the /Pages tree nodes: the page tree is nested, so /Count
# is per node and never the total
pages=$(LC_ALL=C grep -ao '/Type */Page[s]*' "$OUT" | grep -vc 'Pages' || true)
slides=$(LC_ALL=C grep -c 'class="slide' index.html || true)
echo "make-pdf: $OUT — $pages pages from $slides slides, $THEME theme"

if [ "$pages" -ne "$slides" ]; then
  echo "make-pdf: page count does not match slide count" >&2
  exit 1
fi
