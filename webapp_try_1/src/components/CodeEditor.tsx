import React from 'react';
import Editor from '@monaco-editor/react';

interface CodeEditorProps {
  code: string;
  onChange: (value: string | undefined) => void;
}

const CodeEditor: React.FC<CodeEditorProps> = ({ code, onChange }) => {
  return (
    <div style={{ height: '60vh', border: '1px solid #ccc' }}>
      <Editor
        height="100%"
        defaultLanguage="go"
        value={code}
        onChange={onChange}
        theme="vs-dark"
        options={{
          minimap: { enabled: true },
          scrollBeyondLastLine: false,
          fontSize: 14,
          automaticLayout: true,
        }}
      />
    </div>
  );
};

export default CodeEditor;
