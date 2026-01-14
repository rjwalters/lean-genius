import { chromium } from 'playwright';

(async () => {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  
  // Intercept the proof module loading
  page.on('console', msg => {
    const text = msg.text();
    if (text.includes('proof') || text.includes('Proof') || text.includes('undefined') || text.includes('motivic')) {
      console.log('CONSOLE:', msg.type(), text);
    }
  });
  
  page.on('pageerror', err => console.log('PAGE ERROR:', err.message));
  
  console.log('Loading local dev server...\n');
  
  await page.goto('http://localhost:5174/proof/motivic-flag-maps', {
    waitUntil: 'domcontentloaded'
  });
  
  // Wait a bit and check what's in the React state
  await page.waitForTimeout(3000);
  
  // Try to extract debug info from the page
  const debugInfo = await page.evaluate(async () => {
    // Check if the proof data module exists in Vite's module system
    const modules = Object.keys((window as any).__vite_modules__ || {});
    const proofModules = modules.filter(m => m.includes('proof'));
    
    return {
      moduleCount: modules.length,
      proofModules: proofModules.slice(0, 10),
    };
  });
  
  console.log('Debug info:', debugInfo);
  
  await browser.close();
})();
