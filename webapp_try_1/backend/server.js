const express = require('express');
const cors = require('cors');
const bodyParser = require('body-parser');
const { exec } = require('child_process');
const { verifyWithPGo } = require('./pgoHandler');
const { analyzeDependencies } = require('./dependencyAnalyzerWrapper');
const fs = require('fs').promises;
const path = require('path');
const { promisify } = require('util');

const execAsync = promisify(exec);
const app = express();
const port = process.env.PORT || 3002;

app.use(cors());
app.use(bodyParser.json());

app.get('/api/test-code', async (req, res) => {
    try {
        const testCode = await fs.readFile(path.join(__dirname, 'test_code.tla'), 'utf8');
        res.json({ testCode });
    } catch (error) {
        console.error('Error reading test code:', error);
        res.status(500).json({ error: 'Failed to read test code' });
    }
});

function isModuleWrapped(code) {
  return code.trim().startsWith('----') && code.includes('MODULE') && code.endsWith('====');
}

async function cleanupTempFiles(baseName) {
  const extensions = ['.tla', '.cfg', '.old'];
  for (const ext of extensions) {
    try {
      await fs.unlink(baseName + ext).catch(() => {});
    } catch (err) {
      console.error(`Error cleaning up ${baseName}${ext}:`, err);
    }
  }
}

app.post('/api/translate', async (req, res) => {
  const tempBaseName = path.join(__dirname, `temp_${Date.now()}`);
  try {
    const { code } = req.body;
    if (!code) {
      return res.status(400).json({ error: 'No PlusCal code provided' });
    }

    // Create a temporary .tla file
    const tempFile = tempBaseName + '.tla';
    
    // If code is already wrapped in a module, use it as is
    const moduleContent = isModuleWrapped(code) ? code : `---- MODULE Temp ----
EXTENDS Integers
(*
--algorithm Test
${code}
*)
====`;

    // Write PlusCal code to temp file
    await fs.writeFile(tempFile, moduleContent, 'utf8');

    // Run the PlusCal translator
    const { stdout, stderr } = await execAsync(
      `java -cp "${path.join(__dirname, 'tools', 'tla2tools.jar')}" pcal.trans ${tempFile}`
    );

    if (stderr) {
      throw new Error(stderr);
    }

    // Read the translated file
    const translatedContent = await fs.readFile(tempFile, 'utf8');

    // Extract the TLA+ translation
    const startMarker = '\\* BEGIN TRANSLATION';
    const endMarker = '\\* END TRANSLATION';
    const start = translatedContent.indexOf(startMarker);
    const end = translatedContent.indexOf(endMarker);

    if (start === -1 || end === -1) {
      throw new Error('Translation markers not found');
    }

    const tlaCode = translatedContent.slice(start, end + endMarker.length);
    res.json({ tlaCode });

  } catch (error) {
    console.error('Translation error:', error);
    res.status(500).json({ error: error.message });
  } finally {
    // Clean up all temporary files
    await cleanupTempFiles(tempBaseName);
  }
});

// Clean up any existing temp files on server start
(async () => {
  try {
    const files = await fs.readdir(__dirname);
    for (const file of files) {
      if (file.startsWith('temp_')) {
        await fs.unlink(path.join(__dirname, file)).catch(() => {});
      }
    }
  } catch (err) {
    console.error('Error cleaning up temp files on startup:', err);
  }
})();

app.post('/api/analyze', async (req, res) => {
  try {
    const { code, trackedVariables, safetyProperties, livenessProperties } = req.body;
    
    // Analyze dependencies
    const condensedCode = await analyzeDependencies(code, trackedVariables);
    
    // Import the PlusCalGenerator class
    const { PlusCalGenerator } = require('./plusCalGenerator');
    
    // Create a new instance of the PlusCalGenerator
    const generator = new PlusCalGenerator();
    
    // Generate PlusCal code using the JavaScript implementation
    const plusCalCode = await generator.generatePlusCal({
      goCode: condensedCode,
      trackedVariables,
      safetyProperties,
      livenessProperties
    });
    
    // Return the generated PlusCal code
    res.json({ plusCalCode });
  } catch (error) {
    console.error('Error in analyze endpoint:', error);
    res.status(500).json({ error: error.message });
  }
});

app.post('/api/verify', (req, res) => {
  const { code } = req.body;
  res.json({ message: 'Verification endpoint' });
});

app.post('/api/verify-pgo', async (req, res) => {
  console.log('Received request for verify-pgo');
  console.log('Request body:', JSON.stringify(req.body, null, 2));
  console.log('PlusCal code:', req.body.plusCalCode);

  const { plusCalCode } = req.body;
  
  if (!plusCalCode) {
    console.log('No PlusCal code provided');
    return res.status(400).json({ error: 'No PlusCal code provided' });
  }

  try {
    console.log('Calling verifyWithPGo...');
    const goCode = await verifyWithPGo(plusCalCode);
    console.log('Generated Go code:', goCode);
    res.json({ goCode });
  } catch (error) {
    console.error('Error in verify-pgo endpoint:', error);
    console.error('Error stack:', error.stack);
    res.status(500).json({ error: error.message });
  }
});

app.listen(port, () => {
  console.log(`Server running on port ${port}`);
});
