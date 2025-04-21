const fetch = (...args) => import('node-fetch').then(({default: fetch}) => fetch(...args));
require('dotenv').config();

class PlusCalGenerator {
  constructor() {
    this.generator = null;
  }

  async initializeGenerator() {
    // No initialization needed for fetch-based calls
    return;
  }

  async generatePlusCal(options) {
    try {
      await this.initializeGenerator();

      const prompt = this.buildPrompt(
        options.goCode,
        options.trackedVariables,
        options.safetyProperties,
        options.livenessProperties
      );

      const response = await fetch('https://go.apis.huit.harvard.edu/ais-openai-direct-limited-schools/v1/chat/completions', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'api-key': process.env.OPENAI_API_KEY,
        },
        body: JSON.stringify({
          model: 'gpt-4.1-mini-2025-04-14',
          messages: [
            { role: 'system', content: 'You are an expert in converting Go code to PlusCal for formal verification.' },
            { role: 'user', content: prompt },
          ],
          max_tokens: 1000,
          temperature: 0.7,
        }),
      });
      if (!response.ok) {
        const errorText = await response.text();
        throw new Error(`Harvard OpenAI proxy error: ${response.status} ${errorText}`);
      }
      const data = await response.json();
      return data.choices[0].message.content.trim();
    } catch (error) {
      console.error('Error generating PlusCal:', error);
      throw error;
    }
  }

  buildPrompt(goCode, trackedVariables, safetyProperties, livenessProperties) {
    return `
    You are an expert in converting Go code to PlusCal for formal verification.
    
    Input Go code:
    ${goCode}
    
    Tracked variables: ${trackedVariables.join(', ')}
    
    Safety properties to verify:
    ${safetyProperties.join('\n')}
    
    Liveness properties to verify:
    ${livenessProperties.join('\n')}
    
    Please generate PlusCal code that:
    1. Preserves the essential behavior of the Go code
    2. Includes proper variable declarations
    3. Implements the specified safety and liveness properties
    4. Follows PlusCal syntax and best practices
    5. Includes proper assertions and invariants
    
    Format the output as a complete PlusCal specification, including:
    - Variable declarations
    - Algorithm structure
    - Assertions and invariants
    - Proper indentation and formatting
    `;
  }
}

module.exports = { PlusCalGenerator };
