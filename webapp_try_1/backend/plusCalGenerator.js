const { pipeline } = require('@xenova/transformers');
require('dotenv').config();

class PlusCalGenerator {
  constructor() {
    this.generator = null;
  }

  async initializeGenerator() {
    if (!this.generator) {
      try {
        this.generator = await pipeline('text-generation', 'meta-llama/Llama-3.2-1B', {
          token: process.env.HUGGING_FACE_TOKEN
        });
      } catch (error) {
        console.error('Failed to initialize LLM:', error);
        throw error;
      }
    }
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

      const result = await this.generator(prompt, {
        max_new_tokens: 1000,
        temperature: 0.7,
        return_full_text: false,
      });

      return result[0].generated_text.trim();
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
