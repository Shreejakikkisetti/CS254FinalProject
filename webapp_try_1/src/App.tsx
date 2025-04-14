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
import TranslatorTest from './components/TranslatorTest';

interface PropertiesFieldProps {
  properties: string;
  onChange: (value: string) => void;
}

interface VariableTrackerProps {
  variables: string;
  onChange: (value: string) => void;
}

const API_BASE_URL = process.env.REACT_APP_API_URL || 'http://localhost:3002';

// Create a separate component for the main content to handle navigation
const MainContent: React.FC = () => {
  const navigate = useNavigate();
  const [code, setCode] = useState<string>(`package main

func main() {
    temp := 100
    target := 70
    
    if temp > target {
        temp = target
    }
}`);
  const [properties, setProperties] = useState<string>('safety:temp <= target');
  const [variables, setVariables] = useState<string>('temp,target');
  const [plusCalResult, setPlusCalResult] = useState<string>('');
  const [isConverting, setIsConverting] = useState<boolean>(false);
  const [error, setError] = useState<string>('');

  const handleConvert = async () => {
    setIsConverting(true);
    setError('');
    
    try {
      // Parse tracked variables
      const parsedVariables = variables.split(',').map(v => v.trim()).filter(v => v);
      
      // Parse properties into safety and liveness
      const safetyProps: string[] = [];
      const livenessProps: string[] = [];
      
      properties.split(',').forEach(prop => {
        const trimmed = prop.trim();
        if (trimmed.startsWith('safety:')) {
          safetyProps.push(trimmed.replace('safety:', '').trim());
        } else if (trimmed.startsWith('liveness:')) {
          livenessProps.push(trimmed.replace('liveness:', '').trim());
        }
      });
      
      // Call the analyze endpoint
      const response = await fetch(`${API_BASE_URL}/api/analyze`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          code,
          trackedVariables: parsedVariables,
          safetyProperties: safetyProps,
          livenessProperties: livenessProps
        })
      });

      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.error || 'Analysis failed');
      }

      const result = await response.json();
      const plusCal = result.plusCalCode;
      
      setPlusCalResult(plusCal);
      navigate('/pluscal', { 
        state: { 
          plusCalCode: plusCal,
          originalGoCode: code
        } 
      });
    } catch (error) {
      console.error('Conversion failed:', error);
      setError(error instanceof Error ? error.message : 'Conversion failed');
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
          onChange={(value: string) => setProperties(value)}
        />
        <Typography variant="caption" color="textSecondary" sx={{ mt: 1 }}>
          Format: safety:property_name or liveness:property_name
        </Typography>
      </Paper>

      <Paper elevation={3} sx={{ p: 2, mb: 2 }}>
        <Typography variant="h6" gutterBottom>
          Tracked Variables
        </Typography>
        <VariableTracker
          variables={variables}
          onChange={(value: string) => setVariables(value)}
        />
        <Typography variant="caption" color="textSecondary" sx={{ mt: 1 }}>
          Comma-separated list of variables to track
        </Typography>
      </Paper>

      {error && (
        <Typography color="error" sx={{ mb: 2 }}>
          {error}
        </Typography>
      )}

      <Button
        variant="contained"
        color="primary"
        onClick={handleConvert}
        disabled={isConverting || !code || !variables}
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
            <Route path="/translator-test" element={
              <TranslatorTest />
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
