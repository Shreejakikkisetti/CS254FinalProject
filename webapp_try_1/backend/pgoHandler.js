const fs = require('fs').promises;
const path = require('path');
const { exec } = require('child_process');
const { promisify } = require('util');
const execAsync = promisify(exec);

const PGO_DIR = path.join(__dirname, 'tools', 'pgo');
const TEMP_DIR = path.join(__dirname, 'temp');

async function ensureTempDir() {
    try {
        await fs.mkdir(TEMP_DIR, { recursive: true });
    } catch (err) {
        if (err.code !== 'EEXIST') {
            throw err;
        }
    }
}

async function cleanupTempFiles(baseName) {
    const extensions = ['.tla', '.go'];
    for (const ext of extensions) {
        try {
            await fs.unlink(baseName + ext).catch(() => {});
        } catch (err) {
            console.error(`Error cleaning up ${baseName}${ext}:`, err);
        }
    }
}

async function verifyWithPGo(plusCalCode) {
    const tempBaseName = path.join(TEMP_DIR, `pgo_temp_${Date.now()}`);
    
    try {
        await ensureTempDir();

        // Create a temporary TLA+ file with the PlusCal code
        const tlaFile = tempBaseName + '.tla';
        const moduleContent = `---- MODULE Temp ----
EXTENDS Integers, Sequences
(*
--algorithm Test
${plusCalCode}
*)
====`;

        await fs.writeFile(tlaFile, moduleContent, 'utf8');

        // Run PGo to generate Go code
        const { stdout, stderr } = await execAsync(`java -jar "${path.join(PGO_DIR, 'pgo.jar')}" -m "${tlaFile}"`);

        if (stderr) {
            throw new Error(`PGo error: ${stderr}`);
        }

        // Read the generated Go file
        const goFile = tempBaseName + '.go';
        const goCode = await fs.readFile(goFile, 'utf8');

        return goCode;
    } catch (error) {
        console.error('PGo verification error:', error);
        throw error;
    } finally {
        // Clean up temporary files
        await cleanupTempFiles(tempBaseName);
    }
}

module.exports = {
    verifyWithPGo
};
