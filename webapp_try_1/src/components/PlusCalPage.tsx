import React, { useState, useCallback } from 'react';
import { Box, Button, Typography, CircularProgress, Alert, Snackbar } from '@mui/material';
import GoCodeCompareModal from './GoCodeCompareModal';
import { useNavigate, useLocation } from 'react-router-dom';
import { toast } from 'react-toastify';
import Editor from '@monaco-editor/react';
import { TLATranslator } from '../utils/tlaTranslator';

import 'react-toastify/dist/ReactToastify.css';

const defaultPlusCal = `(* --algorithm sample
variables lock = "FREE";

process p1 = 1
begin
  A1: if lock = "FREE" then
        lock := "HELD";
        print "Process 1 acquired lock";
      end if;
  A2: lock := "FREE";
end process;

process p2 = 2
begin
  B1: if lock = "FREE" then
        lock := "HELD";
        print "Process 2 acquired lock";
      end if;
  B2: lock := "FREE";
end process;
end algorithm; *)`;

const PlusCalPage: React.FC = () => {
    const navigate = useNavigate();
    const location = useLocation();
    const [plusCalCode, setPlusCalCode] = useState(location.state?.plusCalCode || defaultPlusCal);
    const [tlaCode, setTlaCode] = useState('');
    const [isLoading, setIsLoading] = useState(false);
    const [error, setError] = useState<string | null>(null);
    const [showError, setShowError] = useState(false);
    const [originalGoCode, setOriginalGoCode] = useState(location.state?.originalGoCode || '');
    const [showCompareModal, setShowCompareModal] = useState(false);
    const [generatedGoCode, setGeneratedGoCode] = useState('');

    const handleTranslate = async () => {
        setIsLoading(true);
        setError(null);
        setShowError(false);
        try {
            const translator = TLATranslator.getInstance();
            const translatedCode = await translator.translateToTLA(plusCalCode);
            setTlaCode(translatedCode);
            toast.success('Translation successful');
        } catch (err: any) {
            setError(err.message);
            setShowError(true);
            setTlaCode('');
            toast.error('Translation failed');
        } finally {
            setIsLoading(false);
        }
    };

    const handleCloseError = () => {
        setShowError(false);
    };

    const handleVerifyWithPGo = async () => {
        setIsLoading(true);
        try {
            // TODO: Make API call to backend to run PGo
            // For now, just show a placeholder comparison
            const response = await fetch('http://localhost:3002/api/verify-pgo', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({
                    plusCalCode
                })
            });

            if (!response.ok) {
                throw new Error('Failed to verify with PGo');
            }

            const data = await response.json();
            setGeneratedGoCode(data.goCode);
            setShowCompareModal(true);
        } catch (err: any) {
            toast.error(err.message || 'Failed to verify with PGo');
            setError(err.message);
            setShowError(true);
        } finally {
            setIsLoading(false);
        }
    };

    return (
        <Box sx={{ p: 3, height: '100vh', display: 'flex', flexDirection: 'column' }}>
            <Typography variant="h4" gutterBottom>
                PlusCal to TLA+ Translator
            </Typography>
            
            {error && (
                <Alert severity="error" sx={{ mb: 2 }}>
                    {error}
                </Alert>
            )}

            <Box sx={{ display: 'flex', gap: 2, mb: 2 }}>
                <Button 
                    variant="contained" 
                    onClick={handleTranslate}
                    disabled={isLoading}
                >
                    {isLoading ? <CircularProgress size={24} /> : 'Translate to TLA+'}
                </Button>
                <Button
                    variant="contained"
                    color="secondary"
                    onClick={handleVerifyWithPGo}
                    disabled={isLoading}
                >
                    Verify with PGo
                </Button>
            </Box>

            <Box sx={{ display: 'flex', gap: 2, flex: 1, minHeight: 0 }}>
                <Box sx={{ flex: 1, display: 'flex', flexDirection: 'column' }}>
                    <Typography variant="h6" gutterBottom>
                        PlusCal Code
                    </Typography>
                    <Box sx={{ flex: 1, border: '1px solid #ccc' }}>
                        <Editor
                            defaultLanguage="plaintext"
                            value={plusCalCode}
                            onChange={(value) => setPlusCalCode(value || '')}
                            options={{
                                minimap: { enabled: false },
                                fontSize: 14,
                                lineNumbers: 'on',
                                scrollBeyondLastLine: false,
                                automaticLayout: true,
                            }}
                        />
                    </Box>
                </Box>

                <Box sx={{ flex: 1, display: 'flex', flexDirection: 'column' }}>
                    <Typography variant="h6" gutterBottom>
                        TLA+ Code
                    </Typography>
                    <Box sx={{ flex: 1, border: '1px solid #ccc' }}>
                        <Editor
                            defaultLanguage="plaintext"
                            value={tlaCode}
                            options={{
                                minimap: { enabled: false },
                                fontSize: 14,
                                lineNumbers: 'on',
                                readOnly: true,
                                scrollBeyondLastLine: false,
                                automaticLayout: true,
                            }}
                        />
                    </Box>
                </Box>
            </Box>
            <Button
                variant="outlined"
                onClick={() => navigate(-1)}
                sx={{ mt: 2 }}
            >
                Back to Go Code
            </Button>

            <Snackbar 
                open={showError} 
                autoHideDuration={6000} 
                onClose={handleCloseError}
                anchorOrigin={{ vertical: 'top', horizontal: 'center' }}
            >
                <Alert 
                    onClose={handleCloseError} 
                    severity="error" 
                    variant="filled"
                    sx={{ width: '100%' }}
                >
                    {error ? `Translation Error: ${error}` : 'An error occurred during translation'}
                </Alert>
            </Snackbar>

            <GoCodeCompareModal
                open={showCompareModal}
                onClose={() => setShowCompareModal(false)}
                originalCode={originalGoCode}
                generatedCode={generatedGoCode}
            />
        </Box>
    );
};

export default PlusCalPage;
