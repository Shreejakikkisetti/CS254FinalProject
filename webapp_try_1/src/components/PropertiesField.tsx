import React from 'react';
import { TextField } from '@mui/material';

interface PropertiesFieldProps {
  properties: string;
  onChange: (value: string) => void;
}

const PropertiesField: React.FC<PropertiesFieldProps> = ({ properties, onChange }) => {
  return (
    <TextField
      label="Verification Properties"
      multiline
      rows={4}
      value={properties}
      onChange={(e) => onChange(e.target.value)}
      fullWidth
      placeholder="Enter properties (e.g., 'SAFETY: No double locking')"
      variant="outlined"
      sx={{ mt: 2 }}
    />
  );
};

export default PropertiesField;
