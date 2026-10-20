// Regression check for #43696: gallery scroll position must survive Back.
//
// Scrolls deep into a gallery route (revealing incremental batches as it
// goes), opens a card, presses Back, and reports the landing offset; then
// checks a fresh navigation to the route starts at the top.
//
// Run against a dev server (`pnpm dev`, default port 5173) with Playwright's
// Chromium installed (`pnpm exec playwright install chromium`):
//
//   BASE=http://localhost:5173 node scripts/tests/gallery-scroll-restoration.cjs
//   ROUTE=/research CARD='a[href^="/research/"]' node scripts/tests/gallery-scroll-restoration.cjs
//
// Expected: drift 0 px and fresh.y 0. On main before the fix, Back landed at
// the bottom of the page (drift of ~170,000 px).
const { chromium } = require('playwright');

const BASE = process.env.BASE || 'http://localhost:5173';
const ROUTE = process.env.ROUTE || '/';
const CARD = process.env.CARD || 'a[href^="/proof/"]';
const TARGET = Number(process.env.TARGET || 60000);

async function state(page) {
  return page.evaluate((sel) => ({
    y: Math.round(window.scrollY),
    height: document.documentElement.scrollHeight,
    cards: document.querySelectorAll(sel).length,
  }), CARD);
}

(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  page.on('pageerror', (e) => console.log('PAGE ERROR', e.message));

  await page.goto(BASE + ROUTE, { waitUntil: 'networkidle' });
  await page.waitForSelector(CARD, { timeout: 90000 });

  // Scroll deep in steps so the incremental list keeps revealing batches.
  for (let i = 0; i < 400; i++) {
    await page.evaluate(() => window.scrollBy(0, 2000));
    await page.waitForTimeout(120);
    const y = await page.evaluate(() => window.scrollY);
    if (y >= TARGET) break;
  }
  await page.waitForTimeout(500);
  const before = await state(page);

  // Open a card that is currently on screen.
  const href = await page.evaluate((sel) => {
    const links = [...document.querySelectorAll(sel)];
    const vis = links.filter((l) => { const r = l.getBoundingClientRect(); return r.top >= 0 && r.bottom <= window.innerHeight; });
    return (vis[0] || links[links.length - 1]).getAttribute('href');
  }, CARD);
  await page.click(`a[href="${href}"]`);
  await page.waitForURL((u) => !u.pathname.endsWith(ROUTE === '/' ? '/#' : ROUTE) && u.pathname !== ROUTE, { timeout: 30000 });
  await page.waitForTimeout(1500);
  const onDetail = Math.round(await page.evaluate(() => window.scrollY));

  // Back.
  await page.goBack();
  await page.waitForSelector(CARD, { timeout: 90000 });
  await page.waitForTimeout(3000);
  const after = await state(page);

  // Fresh visit from the detail page via a normal link: must start at the top.
  await page.goto(BASE + href, { waitUntil: 'networkidle' });
  await page.evaluate(() => window.scrollTo(0, 2500));
  await page.waitForTimeout(300);
  const navLink = await page.$(`a[href="${ROUTE}"]`);
  let fresh = null;
  if (navLink) {
    await navLink.click();
    await page.waitForSelector(CARD, { timeout: 90000 });
    await page.waitForTimeout(1500);
    fresh = await state(page);
  }

  console.log(JSON.stringify({ route: ROUTE, href, before, onDetail, after, drift: Math.abs(after.y - before.y), fresh }, null, 1));
  await browser.close();
})().catch((e) => { console.error('FAILED', e); process.exit(1); });
