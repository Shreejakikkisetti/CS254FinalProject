package elevatorcontrol

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
		Name: "ElevatorController.mainLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			doorOpen, err := iface.RequireArchetypeResourceRef("ElevatorController.doorOpen")
			if err != nil {
				return err
			}
			currentFloor, err := iface.RequireArchetypeResourceRef("ElevatorController.currentFloor")
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
					return iface.Goto("ElevatorController.mainLoop")
				} else {
					err = iface.Write(doorOpen, nil, tla.ModuleFALSE)
					if err != nil {
						return err
					}
					var condition0 tla.Value
					condition0, err = iface.Read(currentFloor, nil)
					if err != nil {
						return err
					}
					if tla.ModuleLessThanSymbol(condition0, tla.MakeNumber(4)).AsBool() {
						var exprRead tla.Value
						exprRead, err = iface.Read(currentFloor, nil)
						if err != nil {
							return err
						}
						err = iface.Write(currentFloor, nil, tla.ModulePlusSymbol(exprRead, tla.MakeNumber(1)))
						if err != nil {
							return err
						}
						return iface.Goto("ElevatorController.mainLoop")
					} else {
						return iface.Goto("ElevatorController.mainLoop")
					}
					// no statements
				}
				// no statements
			} else {
				return iface.Goto("ElevatorController.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ElevatorController.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ElevatorController = distsys.MPCalArchetype{
	Name:              "ElevatorController",
	Label:             "ElevatorController.mainLoop",
	RequiredRefParams: []string{"ElevatorController.currentFloor", "ElevatorController.doorOpen"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
