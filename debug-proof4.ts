import { chromium } from 'playwright';

(async () => {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  
  let hadError = false;
  page.on('pageerror', err => {
    hadError = true;
    console.log('PAGE ERROR:', err.message);
  });
  
  console.log('Testing page after fix...\n');
  
  await page.goto('http://localhost:5174/proof/motivic-flag-maps', {
    waitUntil: 'networkidle',
    timeout: 30000
  });
  
  await page.waitForTimeout(2000);
  
  if (!hadError) {
    console.log('✓ No JavaScript errors!');
  }
  
  // Check page content
  const title = await page.title();
  console.log('Title:', title);
  
  const h1 = await page.$('h1');
  if (h1) {
    console.log('H1 text:', await h1.textContent());
  }
  
  // Check if proof content is visible
  const hasProofContent = await page.$eval('body', el => 
    el.textContent?.includes('Motivic Class') || el.textContent?.includes('flag')
  );
  console.log('Has proof content:', hasProofContent);
  
  // Take a screenshot for verification
  await page.screenshot({ path: '/tmp/proof-page.png', fullPage: false });
  console.log('\nScreenshot saved to /tmp/proof-page.png');
  
  await browser.close();
})();
