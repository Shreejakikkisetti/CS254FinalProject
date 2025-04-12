export class TLATranslator {
  private static instance: TLATranslator;
  private baseUrl: string;

  private constructor() {
    this.baseUrl = 'http://localhost:3002';
  }

  public static getInstance(): TLATranslator {
    if (!TLATranslator.instance) {
      TLATranslator.instance = new TLATranslator();
    }
    return TLATranslator.instance;
  }

  /**
   * Translates PlusCal code to TLA+
   * @param plusCalCode The PlusCal code to translate
   * @returns The translated TLA+ code
   */
  public async translateToTLA(plusCalCode: string): Promise<string> {
    try {
      // Remove any trailing newlines and add one newline at the end
      plusCalCode = plusCalCode.trim() + '\n';
      
      console.log('Sending request to backend with code:', plusCalCode);
      const response = await fetch(`${this.baseUrl}/api/translate`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ code: plusCalCode }),
      });

      if (!response.ok) {
        const errorData = await response.json();
        throw new Error(errorData.error || 'Translation failed');
      }

      const data = await response.json();
      if (!data.tlaCode) {
        throw new Error('No translation received from server');
      }
      return data.tlaCode;
    } catch (error: any) {
      console.error('Translation error:', error);
      throw new Error(`Translation failed: ${error.message}`);
    }
  }
}
