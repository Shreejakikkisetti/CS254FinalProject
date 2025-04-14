package dependencyanalyzer

import (
	"strings"
	"testing"
)

func TestDependencyAnalysis(t *testing.T) {
	code := `package main

func main() {
	// Variables we care about
	temp := 100
	target := 70
	
	// Variables we don't care about
	humidity := 50
	pressure := 1000
	
	// Some unrelated code
	if humidity > 60 {
		pressure += 10
	}
	
	// Code that affects our variables
	if temp > target {
		// This should be included
		temp = target
	} else if humidity < 30 {
		// This should be excluded
		pressure -= 5
	}
	
	// More unrelated code
	if pressure > 1020 {
		humidity += 5
	}
}`
	
	analyzer := NewDependencyAnalyzer()
	analyzer.SetTrackedVariables([]string{"temp", "target"})
	
	result, err := analyzer.AnalyzeCode(code)
	if err != nil {
		t.Errorf("Analysis failed: %v", err)
	}
	
	// The result should only contain code related to temp and target
	expected := `package main

func main() {
	temp := 100
	target := 70
	
	if temp > target {
		temp = target
	}
}`
	
	// Normalize whitespace for comparison
	result = strings.TrimSpace(result)
	expected = strings.TrimSpace(expected)
	
	if result != expected {
		t.Errorf("\nExpected:\n%s\n\nGot:\n%s", expected, result)
	}
}
