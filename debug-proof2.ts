import { chromium } from 'playwright';

(async () => {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  
  page.on('pageerror', err => {
    console.log('PAGE ERROR:', err.message);
  });
  
  console.log('Testing module loading...\n');
  
  await page.goto('http://localhost:5174/', {
    waitUntil: 'networkidle',
    timeout: 30000
  });
  
  // Inject test code to load the module directly
  const result = await page.evaluate(async () => {
    // Dynamically import the proofs module
    const proofIndex = await import('/src/data/proofs/index.ts');
    
    // Test getProofAsync
    const proofData = await proofIndex.getProofAsync('motivic-flag-maps');
    
    if (!proofData) {
      return { error: 'getProofAsync returned undefined' };
    }
    
    return {
      hasProof: !!proofData.proof,
      hasAnnotations: !!proofData.annotations,
      proofKeys: proofData.proof ? Object.keys(proofData.proof) : null,
      annotationsLength: proofData.annotations?.length,
      proofId: proofData.proof?.id,
      proofTitle: proofData.proof?.title,
      proofSlug: proofData.proof?.slug,
      proofDescription: proofData.proof?.description?.slice(0, 50),
      hasOverview: !!proofData.proof?.overview,
      hasMeta: !!proofData.proof?.meta,
    };
  });
  
  console.log('Module load result:');
  console.log(JSON.stringify(result, null, 2));
  
  await browser.close();
})();
