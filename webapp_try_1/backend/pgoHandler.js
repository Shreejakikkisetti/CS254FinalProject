const fs = require('fs').promises;
const path = require('path');
const { exec } = require('child_process');
const { promisify } = require('util');
const execAsync = promisify(exec);

const EXAMPLES_DIR = path.join(__dirname, 'examples');

async function verifyWithPGo(tlaContent) {
    try {
        console.log('Starting PGo verification...');
        
        // Create a unique filename for this conversion
        const timestamp = Date.now();
        const specFile = path.join(EXAMPLES_DIR, `spec_${timestamp}.tla`);
        const outFile = path.join(EXAMPLES_DIR, `spec_${timestamp}.go`);

        console.log('Using files:', { specFile, outFile });

        // Write the TLA+ specification file
        console.log('Writing TLA+ specification file...');
        await fs.writeFile(specFile, tlaContent, 'utf8');

        // Run scala-cli to generate Go code
        console.log('Running PGo command...');
        const command = `scala-cli run . -- gogen --spec-file "${specFile}" --out-file "${outFile}"`;
        
        const { stdout, stderr } = await execAsync(command, { cwd: __dirname });
        if (stderr) {
            console.error('PGo stderr:', stderr);
        }

        // Read the generated Go file
        let goCode;
        try {
            console.log('Reading generated Go file...');
            goCode = await fs.readFile(outFile, 'utf8');

            // Format the Go code
            try {
                await execAsync('go fmt ' + outFile, { cwd: __dirname });
                goCode = await fs.readFile(outFile, 'utf8');
            } catch (err) {
                console.warn('Failed to format Go code:', err);
            }
        } catch (err) {
            console.error('Failed to read Go file:', err);
            throw new Error(`PGo failed to generate Go code: ${stderr}`);
        }

        // Clean up the files
        await Promise.all([
            fs.unlink(specFile).catch((err) => console.error('Failed to delete spec file:', err)),
            fs.unlink(outFile).catch((err) => console.error('Failed to delete output file:', err))
        ]);

        return goCode;
    } catch (error) {
        console.error('PGo verification error:', error);
        throw error;
    }
}

module.exports = {
    verifyWithPGo
};
