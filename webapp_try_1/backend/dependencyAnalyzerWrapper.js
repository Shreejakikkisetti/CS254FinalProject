const { execSync } = require('child_process');
const fs = require('fs').promises;
const path = require('path');

const TEMP_DIR = path.join(__dirname, 'temp');
const ANALYZER_DIR = path.join(__dirname, 'dependency-analyzer');

async function analyzeDependencies(code, trackedVariables) {
  try {
    // Create temp directory if it doesn't exist
    await fs.mkdir(TEMP_DIR, { recursive: true });

    // Write code to temp file
    const codeFile = path.join(TEMP_DIR, 'code.go');
    await fs.writeFile(codeFile, code);

    // Write tracked variables to temp file
    const varsFile = path.join(TEMP_DIR, 'variables.txt');
    await fs.writeFile(varsFile, trackedVariables.join('\n'));

    // Run the Go dependency analyzer
    const result = execSync(
      `go run cmd/main.go -code ${codeFile} -vars ${varsFile}`,
      { cwd: ANALYZER_DIR }
    ).toString();

    // Parse the JSON response
    const response = JSON.parse(result);
    
    // TODO: Once LLM is integrated, process its results here

    return response;
  } catch (error) {
    console.error('Error analyzing dependencies:', error);
    throw error;
  } finally {
    // Clean up temp files
    try {
      await fs.rm(TEMP_DIR, { recursive: true, force: true });
    } catch (err) {
      console.error('Error cleaning up temp files:', err);
    }
  }
}

module.exports = {
  analyzeDependencies
};
