import React, { useState } from 'react';
import { Container, Paper, Typography, Box, Button } from '@mui/material';
import { BrowserRouter as Router, Routes, Route, useNavigate, Navigate, useLocation } from 'react-router-dom';
import { ToastContainer, toast } from 'react-toastify';
import 'react-toastify/dist/ReactToastify.css';
import './App.css';
import CodeEditor from './components/CodeEditor';
import PropertiesField from './components/PropertiesField';
import VariableTracker from './components/VariableTracker';
import PlusCalPage from './components/PlusCalPage';

// Create a separate component for the main content to handle navigation
const MainContent: React.FC = () => {
  const navigate = useNavigate();
  const [code, setCode] = useState<string>('');
  const [properties, setProperties] = useState<string>('');
  const [variables, setVariables] = useState<string>('');
  const [plusCalResult, setPlusCalResult] = useState<string>('');
  const [isConverting, setIsConverting] = useState<boolean>(false);

  const handleConvert = async () => {
    setIsConverting(true);
    try {
      // Show TODO popup
      toast.info('TODO: Implement LLM conversion');
      
      // Generate placeholder PlusCal
      const plusCal = `(* This is a placeholder PlusCal result *)
\* Converted from Go code with properties: ${properties}
\* Tracked variables: ${variables}

BEGIN
  (* Your PlusCal specification will go here *)
END`;
      
      setPlusCalResult(plusCal);
      // Navigate to PlusCal page with state
      navigate('/pluscal', { state: { plusCalCode: plusCal } });
    } catch (error) {
      console.error('Conversion failed:', error);
      setPlusCalResult('Conversion failed. Please check your input and try again.');
    } finally {
      setIsConverting(false);
    }
  };

  return (
    <Box>
      <Paper elevation={3} sx={{ p: 2, mb: 2 }}>
        <Typography variant="h6" gutterBottom>
          Go Code Input
        </Typography>
        <CodeEditor
          code={code}
          onChange={(value) => setCode(value || '')}
        />
      </Paper>

      <Paper elevation={3} sx={{ p: 2, mb: 2 }}>
        <Typography variant="h6" gutterBottom>
          Verification Properties
        </Typography>
        <PropertiesField
          properties={properties}
          onChange={setProperties}
        />
      </Paper>

      <Paper elevation={3} sx={{ p: 2, mb: 2 }}>
        <Typography variant="h6" gutterBottom>
          Variable Tracking
        </Typography>
        <VariableTracker
          variables={variables}
          onChange={setVariables}
        />
      </Paper>

      <Button
        variant="contained"
        color="primary"
        onClick={handleConvert}
        disabled={isConverting || !code}
        sx={{ mt: 2 }}
      >
        {isConverting ? 'Converting...' : 'Convert to PlusCal'}
      </Button>
    </Box>
  );
};

function App() {
  return (
    <Router>
      <Container maxWidth="lg">
        <Box sx={{ my: 4 }}>
          <Typography variant="h4" component="h1" gutterBottom>
            Go2TLA+ Verification Platform
          </Typography>
          
          <Routes>
            <Route path="/" element={
              <MainContent />
            } />
            
            <Route path="/pluscal" element={
              <PlusCalPage />
            } />
            <Route path="*" element={<Navigate to="/" replace />} />
          </Routes>
        </Box>
      </Container>
      <ToastContainer position="top-right" />
    </Router>
  );
}

export default App;
