package doorcontrol

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
		Name: "DoorController.mainLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			doorOpen, err := iface.RequireArchetypeResourceRef("DoorController.doorOpen")
			if err != nil {
				return err
			}
			direction, err := iface.RequireArchetypeResourceRef("DoorController.direction")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				var condition tla.Value
				condition, err = iface.Read(doorOpen, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition, tla.ModuleFALSE).AsBool() {
					err = iface.Write(doorOpen, nil, tla.ModuleTRUE)
					if err != nil {
						return err
					}
					err = iface.Write(direction, nil, iface.GetConstant("in")())
					if err != nil {
						return err
					}
					// no statements
				} else {
					err = iface.Write(doorOpen, nil, tla.ModuleFALSE)
					if err != nil {
						return err
					}
					err = iface.Write(direction, nil, iface.GetConstant("none")())
					if err != nil {
						return err
					}
					// no statements
				}
				var condition0 tla.Value
				condition0, err = iface.Read(doorOpen, nil)
				if err != nil {
					return err
				}
				var condition1 tla.Value
				condition1, err = iface.Read(direction, nil)
				if err != nil {
					return err
				}
				if !tla.MakeBool(!tla.ModuleEqualsSymbol(condition0, tla.ModuleTRUE).AsBool() || tla.ModuleEqualsSymbol(condition1, iface.GetConstant("in")()).AsBool()).AsBool() {
					return fmt.Errorf("%w: ((doorOpen) = (TRUE)) => ((direction) = (in))", distsys.ErrAssertionFailed)
				}
				var condition2 tla.Value
				condition2, err = iface.Read(doorOpen, nil)
				if err != nil {
					return err
				}
				var condition3 tla.Value
				condition3, err = iface.Read(direction, nil)
				if err != nil {
					return err
				}
				if !tla.MakeBool(!tla.ModuleEqualsSymbol(condition2, tla.ModuleFALSE).AsBool() || tla.ModuleEqualsSymbol(condition3, iface.GetConstant("none")()).AsBool()).AsBool() {
					return fmt.Errorf("%w: ((doorOpen) = (FALSE)) => ((direction) = (none))", distsys.ErrAssertionFailed)
				}
				return iface.Goto("DoorController.mainLoop")
			} else {
				return iface.Goto("DoorController.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "DoorController.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var DoorController = distsys.MPCalArchetype{
	Name:              "DoorController",
	Label:             "DoorController.mainLoop",
	RequiredRefParams: []string{"DoorController.doorOpen", "DoorController.direction"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}