import json
import subprocess
from plus_cal_generator import PlusCalGenerator

def test_plus_cal_generator():
    # Create generator instance
    generator = PlusCalGenerator()
    
    try:
        # Test with a simple prompt
        print("Testing with simple prompt...")
        simple_prompt = "What is the capital of France?"
        try:
            simple_result = generator.pipe(
                simple_prompt,
                max_length=20,  # Very short response
                max_new_tokens=10,  # Generate only 10 new tokens
                temperature=0.7,
                top_p=0.9,
                do_sample=True,
                truncation=True,
                pad_token_id=generator.tokenizer.eos_token_id if generator.tokenizer else None
            )
            print("Simple prompt result:", simple_result[0]['generated_text'])
        except Exception as e:
            print(f"Simple prompt failed: {e}")
        
        # Test with PlusCal generation
        print("\nTesting PlusCal generation...")
        test_data = {
            "goCode": "package main\nfunc main() {\n    temp := 100\n    target := 70\n    \n    if temp > target {\n        temp = target\n    }\n}",
            "trackedVariables": ["temp", "target"],
            "safetyProperties": ["temp <= target"],
            "livenessProperties": []
        }
        result = generator.generate_plus_cal(test_data)
        
        # Check if result is not empty
        if not result:
            print("Test failed: Empty result")
            return
            
        print("Generated PlusCal:", result)
        print("Test passed!")
    except ValueError as ve:
        print(f"Test failed (ValueError): {ve}")
        return
    except Exception as e:
        print(f"Test failed (Unexpected error): {e}")
        return False

if __name__ == "__main__":
    success = test_plus_cal_generator()
    if success:
        print("\nTest passed!")
    else:
        print("\nTest failed!")
