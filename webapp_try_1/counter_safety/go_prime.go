package valuecheck

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
		Name: "ValueController.mainLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			value, err := iface.RequireArchetypeResourceRef("ValueController.value")
			if err != nil {
				return err
			}
			var condition tla.Value
			condition, err = iface.Read(value, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition, tla.MakeNumber(4)).AsBool() {
				var exprRead tla.Value
				exprRead, err = iface.Read(value, nil)
				if err != nil {
					return err
				}
				err = iface.Write(value, nil, tla.ModulePercentSymbol(tla.ModulePlusSymbol(exprRead, tla.MakeNumber(1)), tla.MakeNumber(4)))
				if err != nil {
					return err
				}
				return iface.Goto("ValueController.mainLoop")
			} else {
				return iface.Goto("ValueController.postLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ValueController.postLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			value2, err := iface.RequireArchetypeResourceRef("ValueController.value")
			if err != nil {
				return err
			}
			var condition0 tla.Value
			condition0, err = iface.Read(value2, nil)
			if err != nil {
				return err
			}
			if !tla.ModuleEqualsSymbol(condition0, tla.MakeNumber(3)).AsBool() {
				return fmt.Errorf("%w: (value) = (3)", distsys.ErrAssertionFailed)
			}
			return iface.Goto("ValueController.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ValueController.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ValueController = distsys.MPCalArchetype{
	Name:              "ValueController",
	Label:             "ValueController.mainLoop",
	RequiredRefParams: []string{"ValueController.value"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
