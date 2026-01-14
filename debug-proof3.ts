import { chromium } from 'playwright';

(async () => {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  
  page.on('pageerror', err => {
    console.log('PAGE ERROR:', err.message);
  });
  
  page.on('console', msg => {
    if (msg.text().includes('DEBUG_PROOF')) {
      console.log('DEBUG:', msg.text());
    }
  });
  
  // Patch the module to add debugging
  await page.addInitScript(() => {
    // Add global debug flag
    (window as any).__DEBUG_PROOF__ = true;
  });
  
  console.log('Testing page render...\n');
  
  await page.goto('http://localhost:5174/proof/motivic-flag-maps', {
    waitUntil: 'domcontentloaded',
    timeout: 30000
  });
  
  // Try to evaluate what's on the page before error
  await page.waitForTimeout(1000);
  
  // Check React state
  const debugInfo = await page.evaluate(() => {
    // Look for React fiber nodes
    const root = document.getElementById('root');
    if (!root) return { error: 'No root element' };
    
    // Check what's visible
    return {
      innerHTML: root.innerHTML.slice(0, 500),
      childCount: root.childElementCount,
    };
  });
  
  console.log('Page state after error:');
  console.log('Child count:', debugInfo.childCount);
  console.log('HTML preview:', debugInfo.innerHTML?.slice(0, 300));
  
  await browser.close();
})();
