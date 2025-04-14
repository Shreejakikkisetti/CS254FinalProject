from transformers import pipeline
from transformers import AutoTokenizer, AutoModelForCausalLM
import json

class PlusCalGenerator:
    def __init__(self):
        self.tokenizer = None
        self.model = None
        self.pipe = None
        self.initialize_generator()

    def initialize_generator(self):
        if self.tokenizer is None or self.model is None:
            try:
                print("Initializing LLM...")
                self.tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3.2-1B")
                self.model = AutoModelForCausalLM.from_pretrained(
                    "meta-llama/Llama-3.2-1B",
                    rope_scaling={"type": "dynamic", "factor": 32.0}
                )
                self.pipe = pipeline(
                    "text-generation",
                    model=self.model,
                    tokenizer=self.tokenizer,
                    model_kwargs={
                        "max_length": 200,
                        "temperature": 0.7,
                        "top_p": 0.9,
                        "do_sample": True,
                        "truncation": True,
                        "pad_token_id": self.tokenizer.eos_token_id if self.tokenizer else None
                    }
                )
                print("LLM initialized successfully")
            except Exception as e:
                print(f"Error initializing LLM: {e}")
                raise

    def generate_plus_cal(self, options):
        try:
            # Validate input parameters
            if not isinstance(options.get('goCode', ''), str):
                raise ValueError("goCode must be a string")
            if not isinstance(options.get('trackedVariables', []), list):
                raise ValueError("trackedVariables must be a list")
            if not isinstance(options.get('safetyProperties', []), list):
                raise ValueError("safetyProperties must be a list")
            if not isinstance(options.get('livenessProperties', []), list):
                raise ValueError("livenessProperties must be a list")

            prompt = self.build_prompt(
                options.get('goCode', ''),
                options.get('trackedVariables', []),
                options.get('safetyProperties', []),
                options.get('livenessProperties', [])
            )

            print("Generating PlusCal code...")
            
            try:
                result = self.pipe(prompt, 
                    max_length=200, 
                    max_new_tokens=100,
                    temperature=0.7, 
                    top_p=0.9, 
                    do_sample=True,
                    truncation=True,
                    pad_token_id=self.tokenizer.eos_token_id
                )
                if not result or not result[0].get('generated_text'):
                    raise ValueError("Model returned empty or invalid response")
                
                generated_text = result[0]['generated_text'].strip()
                print(f"Generated PlusCal: {generated_text}")
                return generated_text
                
            except Exception as model_error:
                print(f"Error in model generation: {str(model_error)}")
                raise ValueError(f"Failed to generate PlusCal code: {str(model_error)}")

        except ValueError as ve:
            print(f"Validation error: {str(ve)}")
            raise
        except Exception as e:
            print(f"Unexpected error generating PlusCal: {str(e)}")
            raise

    def build_prompt(self, go_code, tracked_variables, safety_properties, liveness_properties):
        prompt = '''
            You are an expert in converting Go code to PlusCal for formal verification.
            
            Input Go code:
            ```go
            {go_code}
            ```
            
            Properties to verify:
            Safety Properties:
            {safety_properties}
            
            Liveness Properties:
            {liveness_properties}
            
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
            
            Example PlusCal format:
            ```
            --algorithm example
            variables
                x = 0;
            begin
                Loop:
                    if
                        :: x < 10
                        -> x := x + 1;
                        :: else
                        -> skip;
                    fi;
            end algorithm;
            '''.format(
                go_code=go_code,
                safety_properties="\n".join(safety_properties),
                liveness_properties="\n".join(liveness_properties)
            )
        return prompt

    def run(self):
        import sys
        import json
        
        # Read from stdin
        input_data = sys.stdin.read()
        options = json.loads(input_data)
        
        try:
            result = self.generate_plus_cal(options)
            print(json.dumps({"success": True, "plusCalCode": result}))
        except Exception as e:
            print(json.dumps({"success": False, "error": str(e)}))

if __name__ == "__main__":
    generator = PlusCalGenerator()
    generator.run()
