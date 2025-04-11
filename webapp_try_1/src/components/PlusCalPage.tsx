import React from 'react';
import { Paper, Typography, Button, Box } from '@mui/material';
import { useNavigate, useLocation } from 'react-router-dom';
import { toast } from 'react-toastify';

import 'react-toastify/dist/ReactToastify.css';

const samplePlusCal = `--algorithm sample
begin
  process p1 = 1
  begin
    with lock \in {FREE, HELD} do
      if lock = FREE then
        lock := HELD;
        print "Process 1 acquired lock";
        lock := FREE;
      end if;
    end with;
  end process;

  process p2 = 2
  begin
    with lock \in {FREE, HELD} do
      if lock = FREE then
        lock := HELD;
        print "Process 2 acquired lock";
        lock := FREE;
      end if;
    end with;
  end process;
end algorithm`;

const PlusCalPage: React.FC = () => {
  const navigate = useNavigate();
  const location = useLocation();
  const plusCalCode = location.state?.plusCalCode || samplePlusCal;

  const handleTranslateToTLA = () => {
    toast.info('TODO: Implement TLA+ translation');
  };

  const handleVerifyWithPGo = () => {
    toast.info('TODO: Implement PGo verification');
  };

  return (
    <Box sx={{ p: 2 }}>
      <Typography variant="h5" gutterBottom>
        PlusCal Specification
      </Typography>

      <Paper elevation={3} sx={{ p: 2, mb: 2 }}>
        <pre style={{ whiteSpace: 'pre-wrap', fontFamily: 'monospace' }}>
          {plusCalCode}
        </pre>
      </Paper>

      <Box sx={{ display: 'flex', gap: 2, mb: 2 }}>
        <Button
          variant="contained"
          color="primary"
          onClick={handleTranslateToTLA}
        >
          Translate to TLA+
        </Button>
        <Button
          variant="contained"
          color="secondary"
          onClick={handleVerifyWithPGo}
        >
          Verify with PGo
        </Button>
      </Box>

      <Button
        variant="outlined"
        onClick={() => navigate(-1)}
        sx={{ mt: 2 }}
      >
        Back to Go Code
      </Button>
    </Box>
  );
};

export default PlusCalPage;
