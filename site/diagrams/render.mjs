import { readFile, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import { fileURLToPath } from "node:url";
import { chromium } from "playwright";

const root = new URL("./", import.meta.url);
const descriptions = {
  "rudin-shrinking-diameter": "Nested disks and successively shorter diameter segments.",
  "rudin-ratio-test": "A row of disks whose radii shrink by a fixed factor.",
  "rudin-power-series": "Exponential partial sums approaching the exponential curve.",
  "rudin-absolute-series": "Alternating signed terms above, and their absolute values below.",
  "rudin-compact-image": "A closed disk maps continuously to a closed oval.",
  "rudin-product-rule": "A rectangle grows by two thin strips and a small corner.",
  "rudin-elementary-derivatives": "A line, parabola, and reciprocal curve with tangent segments.",
  "rudin-exponential-remainder": "An exponential curve and tangent, beside the remainder and a quadratic upper bound.",
  "rudin-sigmoid-slope": "A sigmoid curve with its bell-shaped derivative.",
  "rudin-forward-tangent": "An input perturbation travels forward through a branching computation.",
  "rudin-softmax-normalization": "Three scores become positive exponential weights and then normalized shares.",

  "rudin-backprop-derivative": "Blue arrows carry values forward; amber arrows carry sensitivities backward through branching paths.",
  "rudin-mlp-gradient": "A small neural network with one amber weight, beside a loss curve and its amber tangent.",

  "rudin-tech-tree": "Metric spaces, limits, series, and derivatives lead to exp and neural networks.",
  "rudin-series": "Shrinking terms add to partial sums that approach a finite limit.",
  "rudin-nonnegative-series": "Increasing partial sums stay below a fixed upper bound.",
  "rudin-derivative": "Secant lines through nearby curve points approach a tangent.",
  "rudin-chain-rule": "A small displacement is rescaled by two successive maps.",

  "rudin-convergent-sequences": "A sequence approaches a fixed limit inside successively smaller balls.",
  "rudin-cauchy-sequences": "Two late terms lie in a ball around the limit; the triangle inequality bounds their distance.",
  "rudin-function-limits": "A punctured input neighborhood maps inside a prescribed ball around the output limit.",
  "rudin-continuous-composition": "Three neighborhoods illustrate the composition of two continuous functions.",

  "rudin-metric-spaces": "Three points form a triangle inside an open Euclidean ball; smaller balls show neighborhoods.",
  "rudin-open-closed": "Left: an open disk with neighborhoods inside it. Right: a closed disk contains a boundary limit point, whose neighborhoods extend outside the disk. Dashed boundaries are excluded; solid boundaries are included.",
  "rudin-closures": "Closing a punctured open disk adds its boundary and its missing center point, highlighted in amber.",
  "rudin-compact-sets": "A closed disk covered by open balls. The right-hand picture retains a finite subcover and discards redundant balls.",
  "rudin-compact-interval": "Planar illustration of Rudin's nested-cell argument: nested squares share a point and eventually fit inside an open ball around it.",


};
const names = process.argv.slice(2);
if (!names.length) names.push(...Object.keys(descriptions));
for (const name of names) if (!(name in descriptions)) throw Error(`Unknown diagram: ${name}`);
const bundle = await readFile(new URL("node_modules/@penrose/core/dist/bundle/index.js", root));
const server = createServer((req, res) => {
  res.setHeader("Content-Type", req.url === "/penrose.js" ? "text/javascript" : "text/html");
  res.end(req.url === "/penrose.js" ? bundle : '<!doctype html><body style="margin:0;background:white"></body>');
});
await new Promise(resolve => server.listen(0, "127.0.0.1", resolve));
let browser;
try {
  browser = await chromium.launch({ executablePath: process.env.CHROME_PATH || "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: true });
  for (const name of names) {
  const page = await browser.newPage({ viewport: { width: 920, height: 500 }, deviceScaleFactor: 2 });
  await page.goto(`http://127.0.0.1:${server.address().port}`);
  const trio = {
    domain: await readFile(new URL(`${name}.domain`, root), "utf8"),
    substance: await readFile(new URL(`${name}.substance`, root), "utf8"),
    style: (name === "rudin-tech-tree" ? "" : await readFile(new URL("common.style", root), "utf8")) +
      await readFile(new URL(`${name}.style`, root), "utf8"),
    variation: `${name}-v1`
  };
  const svg = await page.evaluate(async ({trio, description, textFree, techTree}) => {
    const penrose = await import("/penrose.js");
    await penrose.__tla;
    const { compile, optimize, toSVG, showError } = penrose;
    const compiled = await compile(trio);
    if (compiled.isErr()) throw Error(showError(compiled.error));
    const optimized = optimize(compiled.value);
    if (optimized.isErr()) throw Error(showError(optimized.error));
    const svg = await toSVG(optimized.value, async () => undefined);
    svg.setAttribute("role", "img");
    svg.setAttribute("aria-label", description);
    document.body.append(svg);
    await document.fonts.ready;
    const bounds = svg.getBBox();
    const width = bounds.width + 40;
    const height = bounds.height + 40;
    svg.setAttribute("viewBox", techTree ? "0 0 920 590" : textFree ? "0 30 920 440" : `${bounds.x - 20} ${bounds.y - 20} ${width} ${height}`);
    svg.setAttribute("width", "920");
    svg.setAttribute("height", String(techTree ? 590 : textFree ? 440 : 920 * height / width));
    return svg.outerHTML;
  }, {trio, description: descriptions[name], techTree: name === "rudin-tech-tree", textFree: name.startsWith("rudin-") && name !== "rudin-tech-tree"});
  await writeFile(new URL(`${name}.svg`, root), svg + "\n");
  await page.locator('svg').first().screenshot({ path: fileURLToPath(new URL(`${name}.png`, root)) });
  await page.close();
  console.log(`Rendered ${name}.svg with Penrose 3.3.0`);
  }
} finally {
  if (browser) await browser.close();
  server.close();
}
