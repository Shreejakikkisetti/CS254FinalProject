import React from 'react';
import { Dialog, DialogTitle, DialogContent, DialogActions, Button, Box } from '@mui/material';
import { DiffEditor } from '@monaco-editor/react';

interface GoCodeCompareModalProps {
    open: boolean;
    onClose: () => void;
    originalCode: string;
    generatedCode: string;
}

const GoCodeCompareModal: React.FC<GoCodeCompareModalProps> = ({
    open,
    onClose,
    originalCode,
    generatedCode
}) => {
    return (
        <Dialog
            open={open}
            onClose={onClose}
            maxWidth="lg"
            fullWidth
            PaperProps={{
                sx: {
                    height: '80vh',
                    display: 'flex',
                    flexDirection: 'column'
                }
            }}
        >
            <DialogTitle>Go Code Comparison</DialogTitle>
            <DialogContent sx={{ flex: 1, display: 'flex', flexDirection: 'column', minHeight: 0 }}>
                <Box sx={{ flex: 1, minHeight: 0 }}>
                    <DiffEditor
                        height="100%"
                        language="go"
                        original={originalCode}
                        modified={generatedCode}
                        options={{
                            readOnly: true,
                            renderSideBySide: true,
                            minimap: { enabled: false },
                            scrollBeyondLastLine: false,
                            automaticLayout: true
                        }}
                        theme="vs-dark"
                    />
                </Box>
            </DialogContent>
            <DialogActions>
                <Button onClick={onClose}>Close</Button>
            </DialogActions>
        </Dialog>
    );
};

export default GoCodeCompareModal;
