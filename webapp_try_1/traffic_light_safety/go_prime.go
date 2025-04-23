package trafficlight

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
		Name: "TrafficController.mainLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			state, err := iface.RequireArchetypeResourceRef("TrafficController.state")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				var condition tla.Value
				condition, err = iface.Read(state, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition, tla.MakeString("Red")).AsBool() {
					err = iface.Write(state, nil, tla.MakeString("Green"))
					if err != nil {
						return err
					}
					// no statements
				} else {
					var condition0 tla.Value
					condition0, err = iface.Read(state, nil)
					if err != nil {
						return err
					}
					if tla.ModuleEqualsSymbol(condition0, tla.MakeString("Green")).AsBool() {
						err = iface.Write(state, nil, tla.MakeString("Yellow"))
						if err != nil {
							return err
						}
						// no statements
					} else {
						var condition1 tla.Value
						condition1, err = iface.Read(state, nil)
						if err != nil {
							return err
						}
						if tla.ModuleEqualsSymbol(condition1, tla.MakeString("Yellow")).AsBool() {
							err = iface.Write(state, nil, tla.MakeString("Red"))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						// no statements
					}
					// no statements
				}
				var condition2 tla.Value
				condition2, err = iface.Read(state, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleInSymbol(condition2, tla.MakeSet(tla.MakeString("Red"), tla.MakeString("Yellow"), tla.MakeString("Green"))).AsBool() {
					return fmt.Errorf("%w: (state) \\in ({\"Red\", \"Yellow\", \"Green\"})", distsys.ErrAssertionFailed)
				}
				return iface.Goto("TrafficController.mainLoop")
			} else {
				return iface.Goto("TrafficController.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "TrafficController.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var TrafficController = distsys.MPCalArchetype{
	Name:              "TrafficController",
	Label:             "TrafficController.mainLoop",
	RequiredRefParams: []string{"TrafficController.state"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
