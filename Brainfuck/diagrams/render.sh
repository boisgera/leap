#!/usr/bin/env bash
# Render every *.mermaid file in this directory to an SVG file next to it.
#
# Nothing is installed in the project: npx keeps mermaid-cli in ~/.npm/_npx.
# Requires Node. Set CHROME to choose the browser used for rendering.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

MERMAID_CLI_VERSION=12.2.0

# Prefer the system Chrome: on Ubuntu 23.10+, AppArmor prevents the Chrome
# downloaded by Puppeteer from starting its sandbox.
chrome="${CHROME:-$(command -v google-chrome || command -v google-chrome-stable || true)}"

mmdc_args=()
if [[ -n "$chrome" ]]; then
    config="$(mktemp --suffix=.json)"
    trap 'rm -f "$config"' EXIT
    printf '{"executablePath": "%s"}\n' "$chrome" > "$config"
    mmdc_args=(--puppeteerConfigFile "$config")
fi

for input in *.mermaid; do
    output="${input%.mermaid}.svg"
    echo "$input -> $output"
    npx --yes "@mermaid-js/mermaid-cli@$MERMAID_CLI_VERSION" \
        "${mmdc_args[@]}" --quiet --input "$input" --output "$output"
    # Mermaid escapes "<" twice in railroad labels, which would display "&lt;".
    sed -i 's/&amp;lt;/\&lt;/g' "$output"
done
