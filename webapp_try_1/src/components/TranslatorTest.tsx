import React, { useState } from 'react';
import { TLATranslator } from '../utils/tlaTranslator';

const TranslatorTest: React.FC = () => {
    const [plusCalCode, setPlusCalCode] = useState(`variables x = 0;

begin
A:
    x := x + 1;
    goto A;`);
    const [tlaCode, setTlaCode] = useState('');
    const [error, setError] = useState<string | null>(null);

    const handleTranslate = async () => {
        try {
            const translator = TLATranslator.getInstance();
            const result = await translator.translateToTLA(plusCalCode);
            setTlaCode(result);
            setError(null);
        } catch (err: any) {
            setError(err?.message || 'Translation failed');
        }
    };

    return (
        <div>
            <h2>PlusCal to TLA+ Translator Test</h2>
            <div>
                <h3>PlusCal Code:</h3>
                <textarea
                    value={plusCalCode}
                    onChange={(e) => setPlusCalCode(e.target.value)}
                    rows={10}
                    cols={50}
                />
            </div>
            <button onClick={handleTranslate}>Translate</button>
            {error && <div style={{ color: 'red' }}>{error}</div>}
            {tlaCode && (
                <div>
                    <h3>TLA+ Translation:</h3>
                    <pre>{tlaCode}</pre>
                </div>
            )}
        </div>
    );
};

export default TranslatorTest;
