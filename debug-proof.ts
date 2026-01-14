import { chromium } from 'playwright';

(async () => {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  
  // Capture all console messages
  page.on('console', msg => {
    console.log('CONSOLE:', msg.type().toUpperCase(), msg.text());
  });
  
  page.on('pageerror', err => {
    console.log('PAGE ERROR:', err.message);
    console.log('STACK:', err.stack);
  });
  
  console.log('Loading lean-genius on port 5174...\n');
  
  await page.goto('http://localhost:5174/proof/motivic-flag-maps', {
    waitUntil: 'networkidle',
    timeout: 30000
  });
  
  // Wait for React to render
  await page.waitForTimeout(3000);
  
  // Check page content
  const title = await page.title();
  
  console.log('\n--- Page Info ---');
  console.log('Title:', title);
  
  // Look for specific elements
  const h1 = await page.$('h1');
  if (h1) {
    console.log('H1:', await h1.textContent());
  }
  
  // Check for loading state
  const loading = await page.$eval('body', el => el.textContent?.includes('Loading proof'));
  console.log('Shows loading:', loading);
  
  // Check for not found state
  const notFound = await page.$eval('body', el => el.textContent?.includes('not found'));
  console.log('Shows not found:', notFound);
  
  // Get any visible error text
  const bodyText = await page.$eval('body', el => el.textContent?.slice(0, 500));
  console.log('\nBody preview:', bodyText?.slice(0, 300));
  
  await browser.close();
})();
