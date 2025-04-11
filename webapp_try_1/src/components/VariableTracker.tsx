import React from 'react';
import { TextField } from '@mui/material';

interface VariableTrackerProps {
  variables: string;
  onChange: (value: string) => void;
}

const VariableTracker: React.FC<VariableTrackerProps> = ({ variables, onChange }) => {
  return (
    <TextField
      label="Variables to Track"
      value={variables}
      onChange={(e) => onChange(e.target.value)}
      fullWidth
      placeholder="Enter comma-separated variables (e.g., 'lockState, counter')"
      variant="outlined"
      sx={{ mt: 2 }}
    />
  );
};

export default VariableTracker;
