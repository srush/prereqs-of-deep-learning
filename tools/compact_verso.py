#!/usr/bin/env python3
"""Keep Verso proof states out of the initial DOM; retain the checked code verbatim."""
import hashlib
from html.parser import HTMLParser
from pathlib import Path
import sys


class ProofStates(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=False)
        self.source = source
        self.lines = [0]
        for line in source.splitlines(keepends=True):
            self.lines.append(self.lines[-1] + len(line))
        self.depth = 0
        self.current = None
        self.ranges = []

    def position(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        if tag != 'span':
            return
        self.depth += 1
        if self.current is None and 'tactic-state' in dict(attrs).get('class', '').split():
            start = self.position()
            self.current = (self.depth, start, start + len(self.get_starttag_text()))

    def handle_endtag(self, tag):
        if tag != 'span':
            return
        if self.current is not None and self.depth == self.current[0]:
            _, start, content = self.current
            self.ranges.append((start, content, self.position()))
            self.current = None
        self.depth -= 1


def compact(source, assets, runtime):
    # Fail visibly if the pinned Verso renderer's initialization changes.
    script_start = source.index('<script>') + len('<script>')
    script_end = source.index('</script>', script_start)
    script = source[script_start:script_end]
    marker = "    document.querySelectorAll('.hl.lean .const.token,"
    if 'window.onload = async () =>' not in script or marker not in script:
        raise ValueError('Unexpected Verso hover initialization; review compact_verso.py')
    branch = '          state.style.display = "block";'
    if script.count(branch) != 1:
        raise ValueError('Unexpected Verso proof-state renderer')
    script = script[:script.index(marker)]
    script = script.replace(branch, '''          if (state.dataset.proofState) {
            state.textContent = 'Loading proof state…';
            fillProofState(state).then(() => tgt._tippy?.popperInstance?.update());
          }
''' + branch)
    script += runtime + '\n};\n'
    source = source[:script_start] + script + source[script_end:]

    parser = ProofStates(source)
    parser.feed(source)
    if parser.current or parser.depth:
        raise ValueError('Unbalanced span markup')
    if not parser.ranges:
        raise ValueError('No proof states found')
    pieces, cursor = [], 0
    restored = []
    for start, content, end in parser.ranges:
        body = source[content:end]
        name = hashlib.sha256(body.encode()).hexdigest() + '.html'
        (assets / name).write_text(body)
        opening = source[start:content]
        replacement = opening[:-1] + f' data-proof-state="-proof-states/{name}">'
        pieces.extend([source[cursor:start], replacement])
        # Verify that externalization is exactly reversible, including Unicode,
        # links, token IDs, nested spans, and whitespace.
        restored.extend([source[cursor:start], opening, (assets / name).read_text()])
        cursor = end
    pieces.append(source[cursor:])
    restored.append(source[cursor:])
    if ''.join(restored) != source:
        raise ValueError('Proof-state externalization changed the rendered content')
    return ''.join(pieces), len(parser.ranges)


def main():
    root = Path(sys.argv[1])
    assets = root / '-proof-states'
    assets.mkdir(exist_ok=True)
    runtime = (Path(__file__).resolve().parent.parent / 'site/lazy-lean.js').read_text()
    for module in ('Home', 'Speedrun'):
        page = root / 'index.html' if module == 'Home' else root / module / 'index.html'
        if not page.exists():
            continue
        source = page.read_text()
        if 'data-proof-state=' in source:
            continue
        result, count = compact(source, assets, runtime)
        page.write_text(result)
        print(f'{module}: {len(source.encode()) / 1e6:.1f} MB → '
              f'{len(result.encode()) / 1e6:.1f} MB; {count} proof states loaded on demand.')

    # Version reading-view assets so cached styles or scripts cannot leave the
    # renamed article with an older layout or without expandable proofs.
    versions = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()[:16]
                for name in ('verso-tufte.css', 'proofs.js', 'contents.js')}
    for page in root.rglob('index.html'):
        source = page.read_text()
        for name, version in versions.items():
            source = source.replace(f'="{name}"', f'="{name}?v={version}"')
        page.write_text(source)

    # Keep existing article links working after the module rename.
    legacy = root / 'PeanoToLeCun'
    legacy.mkdir(exist_ok=True)
    (legacy / 'index.html').write_text('''<!doctype html>
<meta charset="utf-8">
<title>Deep Learning Speedrun</title>
<meta http-equiv="refresh" content="0; url=../Speedrun/">
<script>location.replace('../Speedrun/' + location.search + location.hash);</script>
<a href="../Speedrun/">Deep Learning Speedrun</a>
''')



if __name__ == '__main__':
    main()
