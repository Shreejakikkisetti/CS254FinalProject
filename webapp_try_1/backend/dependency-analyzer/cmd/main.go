package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"strings"

	"dependency-analyzer/src"
)

func main() {
	// Parse command line arguments
	codeFile := flag.String("code", "", "Path to the Go code file")
	varsFile := flag.String("vars", "", "Path to the tracked variables file")
	flag.Parse()

	if *codeFile == "" || *varsFile == "" {
		fmt.Fprintf(os.Stderr, "Both code and vars files must be specified\n")
		os.Exit(1)
	}

	// Read the Go code
	code, err := ioutil.ReadFile(*codeFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading code file: %v\n", err)
		os.Exit(1)
	}

	// Read the tracked variables
	varsBytes, err := ioutil.ReadFile(*varsFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading vars file: %v\n", err)
		os.Exit(1)
	}
	vars := strings.Split(strings.TrimSpace(string(varsBytes)), "\n")

	// Create and configure the analyzer
	analyzer := dependencyanalyzer.NewDependencyAnalyzer()
	analyzer.SetTrackedVariables(vars)

	// Analyze the code
	result, err := analyzer.AnalyzeCode(string(code))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error analyzing code: %v\n", err)
		os.Exit(1)
	}

	// Create response object
	response := struct {
		CondensedCode string `json:"condensedCode"`
		// TODO: Add LLM analysis results here
	}{
		CondensedCode: result,
	}

	// Output JSON response
	json.NewEncoder(os.Stdout).Encode(response)
}
