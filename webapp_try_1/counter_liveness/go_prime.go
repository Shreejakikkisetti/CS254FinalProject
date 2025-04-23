package counteralgorithm

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "CounterProcess.mainLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			counter, err := iface.RequireArchetypeResourceRef("CounterProcess.counter")
			if err != nil {
				return err
			}
			var condition tla.Value
			condition, err = iface.Read(counter, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition, tla.MakeNumber(4)).AsBool() {
				var exprRead tla.Value
				exprRead, err = iface.Read(counter, nil)
				if err != nil {
					return err
				}
				err = iface.Write(counter, nil, tla.ModulePercentSymbol(tla.ModulePlusSymbol(exprRead, tla.MakeNumber(1)), tla.MakeNumber(4)))
				if err != nil {
					return err
				}
				return iface.Goto("CounterProcess.mainLoop")
			} else {
				return iface.Goto("CounterProcess.postLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "CounterProcess.postLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			counter2, err := iface.RequireArchetypeResourceRef("CounterProcess.counter")
			if err != nil {
				return err
			}
			var condition0 tla.Value
			condition0, err = iface.Read(counter2, nil)
			if err != nil {
				return err
			}
			if !tla.ModuleEqualsSymbol(condition0, tla.MakeNumber(3)).AsBool() {
				return fmt.Errorf("%w: (counter) = (3)", distsys.ErrAssertionFailed)
			}
			return iface.Goto("CounterProcess.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "CounterProcess.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var CounterProcess = distsys.MPCalArchetype{
	Name:              "CounterProcess",
	Label:             "CounterProcess.mainLoop",
	RequiredRefParams: []string{"CounterProcess.counter"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
