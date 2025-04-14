package dependencyanalyzer

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
)

type DependencyAnalyzer struct {
	dependencyGraph map[string][]string
	trackedVars     []string
	initialValues   map[string]string
	conditions      map[string][]string
	assignments    map[string][]string
}

func NewDependencyAnalyzer() *DependencyAnalyzer {
	return &DependencyAnalyzer{
		dependencyGraph: make(map[string][]string),
		trackedVars:     []string{},
		initialValues:   make(map[string]string),
		conditions:      make(map[string][]string),
		assignments:    make(map[string][]string),
	}
}

func (a *DependencyAnalyzer) SetTrackedVariables(vars []string) {
	a.trackedVars = vars
}

func (a *DependencyAnalyzer) AnalyzeCode(code string) (string, error) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "", code, parser.AllErrors)
	if err != nil {
		return "", fmt.Errorf("failed to parse code: %v", err)
	}

	var conf types.Config
	pkg, err := conf.Check("", fset, []*ast.File{f}, nil)
	if err != nil {
		return "", fmt.Errorf("failed to type check: %v", err)
	}

	// First, analyze the AST to find all dependencies
	a.analyzeDependencies(pkg)

	// Then walk the AST to collect all relevant code
	ast.Inspect(f, func(n ast.Node) bool {
		switch node := n.(type) {
		case *ast.AssignStmt:
			// Track assignments
			for i, lhs := range node.Lhs {
				if ident, ok := lhs.(*ast.Ident); ok {
					if a.isTrackedVar(ident.Name) {
						// Store the initial value
						if node.Tok == token.DEFINE {
							a.initialValues[ident.Name] = a.nodeToString(node.Rhs[i])
						}
						// Store the assignment
						a.assignments[ident.Name] = append(a.assignments[ident.Name], a.nodeToString(node))
					}
				}
			}
		case *ast.IfStmt:
			// Track conditions that affect our variables
			for _, name := range a.trackedVars {
				if a.conditionAffectsVar(node, name) {
					a.conditions[name] = append(a.conditions[name], a.nodeToString(node.Cond))
				}
			}
		}
		return true
	})

	// Generate condensed code
	return a.generateCondensedCode(pkg), nil
}

func (a *DependencyAnalyzer) analyzeDependencies(pkg *types.Package) {
	for _, name := range a.trackedVars {
		if obj := pkg.Scope().Lookup(name); obj != nil {
			a.dependencyGraph[name] = []string{}
			a.conditions[name] = []string{}
			a.assignments[name] = []string{}
		}
	}
}

func (a *DependencyAnalyzer) generateCondensedCode(pkg *types.Package) string {
	var result strings.Builder
	result.WriteString("package main\n\n")
	result.WriteString("func main() {\n")
	
	// Track what we've already written to avoid duplicates
	written := make(map[string]bool)
	
	// Add variable declarations with initial values
	for _, name := range a.trackedVars {
		if initialValue, ok := a.initialValues[name]; ok {
			result.WriteString(fmt.Sprintf("\t%s := %s\n", name, initialValue))
			written[fmt.Sprintf("%s := %s", name, initialValue)] = true
		} else if obj := pkg.Scope().Lookup(name); obj != nil {
			result.WriteString(fmt.Sprintf("\tvar %s int\n", name))
		}
	}
	
	// Add a blank line after declarations
	result.WriteString("\n")
	
	// Track written conditions to avoid duplicates
	writtenConds := make(map[string]bool)
	
	// Add conditions and their associated assignments
	for _, name := range a.trackedVars {
		// Add conditions
		if conditions, ok := a.conditions[name]; ok {
			for _, cond := range conditions {
				// Skip if we've already written this condition
				if writtenConds[cond] {
					continue
				}
				writtenConds[cond] = true
				
				result.WriteString(fmt.Sprintf("\tif %s {\n", cond))
				// Add assignments within this condition
				if assignments, ok := a.assignments[name]; ok {
					for _, assign := range assignments {
						// Skip if we've already written this assignment
						if written[assign] {
							continue
						}
						written[assign] = true
						result.WriteString(fmt.Sprintf("\t\t%s\n", assign))
					}
				}
				result.WriteString("\t}\n")
			}
		}
	}
	
	result.WriteString("\n}")
	return result.String()
}

// Helper function to check if a variable is being tracked
func (a *DependencyAnalyzer) isTrackedVar(name string) bool {
	for _, v := range a.trackedVars {
		if v == name {
			return true
		}
	}
	return false
}

// Helper function to convert an AST node to a string
func (a *DependencyAnalyzer) nodeToString(node ast.Node) string {
	switch n := node.(type) {
	case *ast.Ident:
		return n.Name
	case *ast.BasicLit:
		return n.Value
	case *ast.BinaryExpr:
		return fmt.Sprintf("%s %s %s", a.nodeToString(n.X), n.Op, a.nodeToString(n.Y))
	case *ast.AssignStmt:
		var lhs, rhs []string
		for _, expr := range n.Lhs {
			lhs = append(lhs, a.nodeToString(expr))
		}
		for _, expr := range n.Rhs {
			rhs = append(rhs, a.nodeToString(expr))
		}
		return fmt.Sprintf("%s %s %s", strings.Join(lhs, ", "), n.Tok, strings.Join(rhs, ", "))
	default:
		return "" // Unsupported node type
	}
}

// Helper function to check if a condition affects a tracked variable
func (a *DependencyAnalyzer) conditionAffectsVar(ifStmt *ast.IfStmt, varName string) bool {
	affects := false
	
	// Check the condition
	ast.Inspect(ifStmt.Cond, func(n ast.Node) bool {
		if ident, ok := n.(*ast.Ident); ok && ident.Name == varName {
			affects = true
			return false
		}
		return true
	})
	
	// Check the body
	ast.Inspect(ifStmt.Body, func(n ast.Node) bool {
		if assign, ok := n.(*ast.AssignStmt); ok {
			for _, lhs := range assign.Lhs {
				if ident, ok := lhs.(*ast.Ident); ok && ident.Name == varName {
					affects = true
					return false
				}
			}
		}
		return true
	})
	
	return affects
}
