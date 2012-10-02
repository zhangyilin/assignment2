//===-- LiveVariables.cpp - Live Variable Analysis for Machine Code -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the LiveVariable analysis pass.  For each machine
// instruction in the function, this pass calculates the set of registers that
// are immediately dead after the instruction (i.e., the instruction calculates
// the value, but it is never used) and the set of registers that are used by
// the instruction, but are never used after the instruction (i.e., they are
// killed).
//
// This class computes live variables using a sparse implementation based on
// the machine code SSA form.  This class computes live variable information for
// each virtual and _register allocatable_ physical register in a function.  It
// uses the dominance properties of SSA form to efficiently compute live
// variables for virtual registers, and assumes that physical registers are only
// live within a single basic block (allowing it to do a single local analysis
// to resolve physical register lifetimes in each basic block).  If a physical
// register is not register allocatable, it is not tracked.  This is useful for
// things like the stack pointer and condition codes.
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/LiveVariables.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
using namespace llvm;

char LiveVariables::ID = 0;
char &llvm::LiveVariablesID = LiveVariables::ID;
INITIALIZE_PASS_BEGIN(LiveVariables, "livevars",
                "Live Variable Analysis", false, false)
INITIALIZE_PASS_DEPENDENCY(UnreachableMachineBlockElim)
INITIALIZE_PASS_END(LiveVariables, "livevars",
                "Live Variable Analysis", false, false)


void LiveVariables::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequiredID(UnreachableMachineBlockElimID);
  AU.setPreservesAll();
  MachineFunctionPass::getAnalysisUsage(AU);
}

MachineInstr *
LiveVariables::VarInfo::findKill(const MachineBasicBlock *MBB) const {
  // MISSING : Return the instruction in Kills that is part of
  //           MBB, or NULL otherwise.
    for (unsigned i = 0, e = Kills.size(); i != e; ++i){
        if (Kills[i]->getParent() == MBB)
            return Kills[i];
    }
    return NULL;


}

void LiveVariables::VarInfo::dump() const {
  dbgs() << "  Alive in blocks: ";
  for (SparseBitVector<>::iterator I = AliveBlocks.begin(),
           E = AliveBlocks.end(); I != E; ++I)
    dbgs() << *I << ", ";
  dbgs() << "\n  Killed by:";
  if (Kills.empty())
    dbgs() << " No instructions.\n";
  else {
    for (unsigned i = 0, e = Kills.size(); i != e; ++i)
      dbgs() << "\n    #" << i << ": " << *Kills[i];
    dbgs() << "\n";
  }
}

/// getVarInfo - Get (possibly creating) a VarInfo object for the given vreg.
LiveVariables::VarInfo &LiveVariables::getVarInfo(unsigned RegIdx) {
  assert(TargetRegisterInfo::isVirtualRegister(RegIdx) &&
         "getVarInfo: not a virtual register!");
  VirtRegInfo.grow(RegIdx);
  return VirtRegInfo[RegIdx];
}

void LiveVariables::MarkVirtRegAliveInBlock(VarInfo& VRInfo,
                                            MachineBasicBlock *DefBlock,
                                            MachineBasicBlock *MBB,
                                    std::vector<MachineBasicBlock*> &WorkList) {

  // Identifier of the BB.
    unsigned BBNum = MBB->getNumber();
  // Check to see if this basic block is one of the killing blocks.  If so,
  // remove it.
  // MISSING: VarInfo is to be marked alive, so instructions in MBB 
  //  do not kill it. Change Kill set accordingly.
    for (unsigned i = 0, e = VRInfo.Kills.size(); i != e; ++i){
        if (VRInfo.Kills[i]->getParent() == MBB) {
            VRInfo.Kills.erase(VRInfo.Kills.begin()+i);
            break;
        }
    }
    // MISSING: Stop the recursion when the current BB is a 
    //   Definition BB of the var.
    if (MBB == DefBlock) return;//find the def

    // Mark the variable known alive in this bb
    if (VRInfo.AliveBlocks.test(BBNum))
        return;  // We already know the block is live

  // MISSING : Update AliveBlocks of the var.
    VRInfo.AliveBlocks.set(BBNum);

  //  assert(MBB != &MF->front() && "Can't find reaching def for virtreg");

  // MISSING: Insert a preceeding BB into the worklist
    WorkList.insert(WorkList.end(), MBB->pred_rbegin(), MBB->pred_rend());
}

void LiveVariables::MarkVirtRegAliveInBlock(VarInfo &VRInfo,
                                            MachineBasicBlock *DefBlock,
                                            MachineBasicBlock *MBB) {
  std::vector<MachineBasicBlock*> WorkList;
  MarkVirtRegAliveInBlock(VRInfo, DefBlock, MBB, WorkList);
  //After this call, only preceeding BBs of MBB in the WorkList

  // MISSING: Implement a Worklist algorithm that marks
  //          the variable as live, proceeds backwards 
  //          , stopping only when the variable is defined.
    while (!WorkList.empty()) {
        MachineBasicBlock *Pred = WorkList.back();
        WorkList.pop_back();
        MarkVirtRegAliveInBlock(VRInfo, DefBlock, Pred, WorkList);
    }


}

// Update liveness information of reg due to a use in MI, inside MBB.

void LiveVariables::HandleVirtRegUse(unsigned reg, MachineBasicBlock *MBB,
                                     MachineInstr *MI) {
  //  assert(MRI->getVRegDef(reg) && "Register use before def!");

  // Identifier of the BB
  unsigned BBNum = MBB->getNumber();
  // Liveness information for virtual register reg
  VarInfo& VRInfo = getVarInfo(reg);


  // MISSING: If MBB is a kill block, then MI is a Kill instruction of reg, and the recursion ends.

  // Check to see if this basic block is already a kill block.
  if (!VRInfo.Kills.empty() && VRInfo.Kills.back()->getParent() == MBB) {
      //already killed in the MBB, updates the Kills to the later one
      VRInfo.Kills.back() = MI;
      return;
  }

  /*
#ifndef NDEBUG
  for (unsigned i = 0, e = VRInfo.Kills.size(); i != e; ++i)
    assert(VRInfo.Kills[i]->getParent() != MBB && "entry should be at end!");
#endif
  */

  // This situation can occur:
  //
  //     ,------.
  //     |      |
  //     |      v
  //     |   t2 = phi ... t1 ...
  //     |      |
  //     |      v
  //     |   t1 = ...
  //     |  ... = ... t1 ...
  //     |      |
  //     `------'
  //
  // where there is a use in a PHI node that's a predecessor to the defining
  // block. We don't want to mark all predecessors as having the value "alive"
  // in this case.
  if (MBB == MRI->getVRegDef(reg)->getParent()) return;

  // Add a new kill entry for this basic block. If this virtual register is
  // already marked as alive in this basic block, that means it is alive in at
  // least one of the successor blocks, it's not a kill.

  
  if (!VRInfo.AliveBlocks.test(BBNum))
    VRInfo.Kills.push_back(MI);

  // Update all dominating blocks to mark them as "known live".

  // MISSING: The variable is alive in all preceeding basic blocks until a definition is found.
  for (MachineBasicBlock::const_pred_iterator PI = MBB->pred_begin(); PI != MBB->pred_end(); ++PI)
      MarkVirtRegAliveInBlock(VRInfo, MRI->getVRegDef(reg)->getParent(), *PI);


}

void LiveVariables::HandleVirtRegDef(unsigned Reg, MachineInstr *MI) {
  VarInfo &VRInfo = getVarInfo(Reg);

  if (VRInfo.AliveBlocks.empty())
    // If vr is not alive in any block, then defaults to dead.
    VRInfo.Kills.push_back(MI);
}

/// FindLastPartialDef - Return the last partial def of the specified register.
/// Also returns the sub-registers that're defined by the instruction.
MachineInstr *LiveVariables::FindLastPartialDef(unsigned Reg,
                                            SmallSet<unsigned,4> &PartDefRegs) {
  unsigned LastDefReg = 0;
  unsigned LastDefDist = 0;
  MachineInstr *LastDef = NULL;
  for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
    unsigned SubReg = *SubRegs;
    MachineInstr *Def = PhysRegDef[SubReg];
    if (!Def)
      continue;
    unsigned Dist = DistanceMap[Def];
    if (Dist > LastDefDist) {
      LastDefReg  = SubReg;
      LastDef     = Def;
      LastDefDist = Dist;
    }
  }

  if (!LastDef)
    return 0;

  PartDefRegs.insert(LastDefReg);
  for (unsigned i = 0, e = LastDef->getNumOperands(); i != e; ++i) {
    MachineOperand &MO = LastDef->getOperand(i);
    if (!MO.isReg() || !MO.isDef() || MO.getReg() == 0)
      continue;
    unsigned DefReg = MO.getReg();
    if (TRI->isSubRegister(Reg, DefReg)) {
      PartDefRegs.insert(DefReg);
      for (MCSubRegIterator SubRegs(DefReg, TRI); SubRegs.isValid(); ++SubRegs)
        PartDefRegs.insert(*SubRegs);
    }
  }
  return LastDef;
}

/// HandlePhysRegUse - Turn previous partial def's into read/mod/writes. Add
/// implicit defs to a machine instruction if there was an earlier def of its
/// super-register.
void LiveVariables::HandlePhysRegUse(unsigned Reg, MachineInstr *MI) {
  MachineInstr *LastDef = PhysRegDef[Reg];
  // If there was a previous use or a "full" def all is well.
  if (!LastDef && !PhysRegUse[Reg]) {
    // Otherwise, the last sub-register def implicitly defines this register.
    // e.g.
    // AH =
    // AL = ... <imp-def EAX>, <imp-kill AH>
    //    = AH
    // ...
    //    = EAX
    // All of the sub-registers must have been defined before the use of Reg!
    SmallSet<unsigned, 4> PartDefRegs;
    MachineInstr *LastPartialDef = FindLastPartialDef(Reg, PartDefRegs);
    // If LastPartialDef is NULL, it must be using a livein register.
    if (LastPartialDef) {
      LastPartialDef->addOperand(MachineOperand::CreateReg(Reg, true/*IsDef*/,
                                                           true/*IsImp*/));
      PhysRegDef[Reg] = LastPartialDef;
      SmallSet<unsigned, 8> Processed;
      for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
        unsigned SubReg = *SubRegs;
        if (Processed.count(SubReg))
          continue;
        if (PartDefRegs.count(SubReg))
          continue;
        // This part of Reg was defined before the last partial def. It's killed
        // here.
        LastPartialDef->addOperand(MachineOperand::CreateReg(SubReg,
                                                             false/*IsDef*/,
                                                             true/*IsImp*/));
        PhysRegDef[SubReg] = LastPartialDef;
        for (MCSubRegIterator SS(SubReg, TRI); SS.isValid(); ++SS)
          Processed.insert(*SS);
      }
    }
  } else if (LastDef && !PhysRegUse[Reg] &&
             !LastDef->findRegisterDefOperand(Reg))
    // Last def defines the super register, add an implicit def of reg.
    LastDef->addOperand(MachineOperand::CreateReg(Reg, true/*IsDef*/,
                                                  true/*IsImp*/));

  // Remember this use.
  PhysRegUse[Reg]  = MI;
  for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs)
    PhysRegUse[*SubRegs] =  MI;
}

/// FindLastRefOrPartRef - Return the last reference or partial reference of
/// the specified register.
MachineInstr *LiveVariables::FindLastRefOrPartRef(unsigned Reg) {
  MachineInstr *LastDef = PhysRegDef[Reg];
  MachineInstr *LastUse = PhysRegUse[Reg];
  if (!LastDef && !LastUse)
    return 0;

  MachineInstr *LastRefOrPartRef = LastUse ? LastUse : LastDef;
  unsigned LastRefOrPartRefDist = DistanceMap[LastRefOrPartRef];
  unsigned LastPartDefDist = 0;
  for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
    unsigned SubReg = *SubRegs;
    MachineInstr *Def = PhysRegDef[SubReg];
    if (Def && Def != LastDef) {
      // There was a def of this sub-register in between. This is a partial
      // def, keep track of the last one.
      unsigned Dist = DistanceMap[Def];
      if (Dist > LastPartDefDist)
        LastPartDefDist = Dist;
    } else if (MachineInstr *Use = PhysRegUse[SubReg]) {
      unsigned Dist = DistanceMap[Use];
      if (Dist > LastRefOrPartRefDist) {
        LastRefOrPartRefDist = Dist;
        LastRefOrPartRef = Use;
      }
    }
  }

  return LastRefOrPartRef;
}

bool LiveVariables::HandlePhysRegKill(unsigned Reg, MachineInstr *MI) {
  MachineInstr *LastDef = PhysRegDef[Reg];
  MachineInstr *LastUse = PhysRegUse[Reg];
  if (!LastDef && !LastUse)
    return false;

  MachineInstr *LastRefOrPartRef = LastUse ? LastUse : LastDef;
  unsigned LastRefOrPartRefDist = DistanceMap[LastRefOrPartRef];
  // The whole register is used.
  // AL =
  // AH =
  //
  //    = AX
  //    = AL, AX<imp-use, kill>
  // AX =
  //
  // Or whole register is defined, but not used at all.
  // AX<dead> =
  // ...
  // AX =
  //
  // Or whole register is defined, but only partly used.
  // AX<dead> = AL<imp-def>
  //    = AL<kill>
  // AX =
  MachineInstr *LastPartDef = 0;
  unsigned LastPartDefDist = 0;
  SmallSet<unsigned, 8> PartUses;
  for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
    unsigned SubReg = *SubRegs;
    MachineInstr *Def = PhysRegDef[SubReg];
    if (Def && Def != LastDef) {
      // There was a def of this sub-register in between. This is a partial
      // def, keep track of the last one.
      unsigned Dist = DistanceMap[Def];
      if (Dist > LastPartDefDist) {
        LastPartDefDist = Dist;
        LastPartDef = Def;
      }
      continue;
    }
    if (MachineInstr *Use = PhysRegUse[SubReg]) {
      PartUses.insert(SubReg);
      for (MCSubRegIterator SS(SubReg, TRI); SS.isValid(); ++SS)
        PartUses.insert(*SS);
      unsigned Dist = DistanceMap[Use];
      if (Dist > LastRefOrPartRefDist) {
        LastRefOrPartRefDist = Dist;
        LastRefOrPartRef = Use;
      }
    }
  }

  if (!PhysRegUse[Reg]) {
    // Partial uses. Mark register def dead and add implicit def of
    // sub-registers which are used.
    // EAX<dead>  = op  AL<imp-def>
    // That is, EAX def is dead but AL def extends pass it.
    PhysRegDef[Reg]->addRegisterDead(Reg, TRI, true);
    for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
      unsigned SubReg = *SubRegs;
      if (!PartUses.count(SubReg))
        continue;
      bool NeedDef = true;
      if (PhysRegDef[Reg] == PhysRegDef[SubReg]) {
        MachineOperand *MO = PhysRegDef[Reg]->findRegisterDefOperand(SubReg);
        if (MO) {
          NeedDef = false;
          assert(!MO->isDead());
        }
      }
      if (NeedDef)
        PhysRegDef[Reg]->addOperand(MachineOperand::CreateReg(SubReg,
                                                 true/*IsDef*/, true/*IsImp*/));
      MachineInstr *LastSubRef = FindLastRefOrPartRef(SubReg);
      if (LastSubRef)
        LastSubRef->addRegisterKilled(SubReg, TRI, true);
      else {
        LastRefOrPartRef->addRegisterKilled(SubReg, TRI, true);
        PhysRegUse[SubReg] = LastRefOrPartRef;
        for (MCSubRegIterator SS(SubReg, TRI); SS.isValid(); ++SS)
          PhysRegUse[*SS] = LastRefOrPartRef;
      }
      for (MCSubRegIterator SS(SubReg, TRI); SS.isValid(); ++SS)
        PartUses.erase(*SS);
    }
  } else if (LastRefOrPartRef == PhysRegDef[Reg] && LastRefOrPartRef != MI) {
    if (LastPartDef)
      // The last partial def kills the register.
      LastPartDef->addOperand(MachineOperand::CreateReg(Reg, false/*IsDef*/,
                                                true/*IsImp*/, true/*IsKill*/));
    else {
      MachineOperand *MO =
        LastRefOrPartRef->findRegisterDefOperand(Reg, false, TRI);
      bool NeedEC = MO->isEarlyClobber() && MO->getReg() != Reg;
      // If the last reference is the last def, then it's not used at all.
      // That is, unless we are currently processing the last reference itself.
      LastRefOrPartRef->addRegisterDead(Reg, TRI, true);
      if (NeedEC) {
        // If we are adding a subreg def and the superreg def is marked early
        // clobber, add an early clobber marker to the subreg def.
        MO = LastRefOrPartRef->findRegisterDefOperand(Reg);
        if (MO)
          MO->setIsEarlyClobber();
      }
    }
  } else
    LastRefOrPartRef->addRegisterKilled(Reg, TRI, true);
  return true;
}

void LiveVariables::HandleRegMask(const MachineOperand &MO) {
  // Call HandlePhysRegKill() for all live registers clobbered by Mask.
  // Clobbered registers are always dead, sp there is no need to use
  // HandlePhysRegDef().
  for (unsigned Reg = 1, NumRegs = TRI->getNumRegs(); Reg != NumRegs; ++Reg) {
    // Skip dead regs.
    if (!PhysRegDef[Reg] && !PhysRegUse[Reg])
      continue;
    // Skip mask-preserved regs.
    if (!MO.clobbersPhysReg(Reg))
      continue;
    // Kill the largest clobbered super-register.
    // This avoids needless implicit operands.
    unsigned Super = Reg;
    for (MCSuperRegIterator SR(Reg, TRI); SR.isValid(); ++SR)
      if ((PhysRegDef[*SR] || PhysRegUse[*SR]) && MO.clobbersPhysReg(*SR))
        Super = *SR;
    HandlePhysRegKill(Super, 0);
  }
}

void LiveVariables::HandlePhysRegDef(unsigned Reg, MachineInstr *MI,
                                     SmallVector<unsigned, 4> &Defs) {
  // What parts of the register are previously defined?
  SmallSet<unsigned, 32> Live;
  if (PhysRegDef[Reg] || PhysRegUse[Reg]) {
    Live.insert(Reg);
    for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs)
      Live.insert(*SubRegs);
  } else {
    for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
      unsigned SubReg = *SubRegs;
      // If a register isn't itself defined, but all parts that make up of it
      // are defined, then consider it also defined.
      // e.g.
      // AL =
      // AH =
      //    = AX
      if (Live.count(SubReg))
        continue;
      if (PhysRegDef[SubReg] || PhysRegUse[SubReg]) {
        Live.insert(SubReg);
        for (MCSubRegIterator SS(SubReg, TRI); SS.isValid(); ++SS)
          Live.insert(*SS);
      }
    }
  }

  // Start from the largest piece, find the last time any part of the register
  // is referenced.
  HandlePhysRegKill(Reg, MI);
  // Only some of the sub-registers are used.
  for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
    unsigned SubReg = *SubRegs;
    if (!Live.count(SubReg))
      // Skip if this sub-register isn't defined.
      continue;
    HandlePhysRegKill(SubReg, MI);
  }

  if (MI)
    Defs.push_back(Reg);  // Remember this def.
}

void LiveVariables::UpdatePhysRegDefs(MachineInstr *MI,
                                      SmallVector<unsigned, 4> &Defs) {
  while (!Defs.empty()) {
    unsigned Reg = Defs.back();
    Defs.pop_back();
    PhysRegDef[Reg]  = MI;
    PhysRegUse[Reg]  = NULL;
    for (MCSubRegIterator SubRegs(Reg, TRI); SubRegs.isValid(); ++SubRegs) {
      unsigned SubReg = *SubRegs;
      PhysRegDef[SubReg]  = MI;
      PhysRegUse[SubReg]  = NULL;
    }
  }
}

// Entry procedure
bool LiveVariables::runOnMachineFunction(MachineFunction &mf) {
  MF = &mf;
  MRI = &mf.getRegInfo();
  TRI = MF->getTarget().getRegisterInfo();

  ReservedRegisters = TRI->getReservedRegs(mf);

  unsigned NumRegs = TRI->getNumRegs();
  PhysRegDef  = new MachineInstr*[NumRegs];
  PhysRegUse  = new MachineInstr*[NumRegs];
  PHIVarInfo = new SmallVector<unsigned, 4>[MF->getNumBlockIDs()];
  std::fill(PhysRegDef,  PhysRegDef  + NumRegs, (MachineInstr*)0);
  std::fill(PhysRegUse,  PhysRegUse  + NumRegs, (MachineInstr*)0);
  PHIJoins.clear();

  // FIXME: LiveIntervals will be updated to remove its dependence on
  // LiveVariables to improve compilation time and eliminate bizarre pass
  // dependencies. Until then, we can't change much in -O0.
  if (!MRI->isSSA())
    report_fatal_error("regalloc=... not currently supported with -O0");

  analyzePHINodes(mf);

  // Calculate live variable information in depth first order on the CFG of the
  // function.  This guarantees that we will see the definition of a virtual
  // register before its uses due to dominance properties of SSA (except for PHI
  // nodes, which are treated as a special case).
  MachineBasicBlock *Entry = MF->begin();
  SmallPtrSet<MachineBasicBlock*,16> Visited;


  for (df_ext_iterator<MachineBasicBlock*, SmallPtrSet<MachineBasicBlock*,16> >
         DFI = df_ext_begin(Entry, Visited), E = df_ext_end(Entry, Visited);
       DFI != E; ++DFI) {
    MachineBasicBlock *MBB = *DFI;

    // Mark live-in registers as live-in.
    SmallVector<unsigned, 4> Defs;
    for (MachineBasicBlock::livein_iterator II = MBB->livein_begin(),
           EE = MBB->livein_end(); II != EE; ++II) {
      assert(TargetRegisterInfo::isPhysicalRegister(*II) &&
             "Cannot have a live-in virtual register!");
      HandlePhysRegDef(*II, 0, Defs);
    }

    // Loop over all of the instructions, processing them.
    DistanceMap.clear();
    unsigned Dist = 0;
  // MISSING: This loop performs DFA from the entry node. Remember
  //          to run it also from the exit node and compare convergence
  //          (number of iterations until no more 
  //           changes to liveness information). 
  //          You will need to be able to detect convergence and keep count
  //          of iterations.
    for (MachineBasicBlock::iterator I = MBB->begin(), E = MBB->end();
         I != E; ++I) {
      MachineInstr *MI = I;
      //MI->dump();
      if (MI->isDebugValue())
        continue;
      DistanceMap.insert(std::make_pair(MI, Dist++));

      // Process all of the operands of the instruction...
      unsigned NumOperandsToProcess = MI->getNumOperands();

      // Unless it is a PHI node.  In this case, ONLY process the DEF, not any
      // of the uses.  They will be handled in other basic blocks.
      if (MI->isPHI())
        NumOperandsToProcess = 1;

      // Clear kill and dead markers. LV will recompute them.
      SmallVector<unsigned, 4> UseRegs;
      SmallVector<unsigned, 4> DefRegs;
      SmallVector<unsigned, 1> RegMasks;
      for (unsigned i = 0; i != NumOperandsToProcess; ++i) {
        MachineOperand &MO = MI->getOperand(i);
        if (MO.isRegMask()) {
          RegMasks.push_back(i);
          continue;
        }
	

        if (!MO.isReg() || MO.getReg() == 0)
          continue;
	// MISSING: Set the operand MO in the current instruction MI to killed or dead accordingly/
	//          UseRegs should contain the identifiers of used virtual registers in MI and
	//          defRegs the identifiers of defined virtual registers in MI.
        unsigned MO_reg = MO.getReg();
        if (MO.isUse()){
            MO.setIsKill (false);//clear kill flag
            if (MO.readsReg()){
                UseRegs.push_back(MO_reg);
            }
        }
        if (MO.isDef()){//The other case
            MO.setIsDead (false);
            DefRegs.push_back(MO_reg);
        }


      }

      // Process all uses.

      // MISSING: For all used registers (both virtual and physical), update liveness, by using the HandleVirtRegUse and HandlePhysRegUse methods.
      for (unsigned i = 0; i < UseRegs.size(); ++i) {
          unsigned MO_reg = UseRegs[i];
          if (TargetRegisterInfo::isVirtualRegister(MO_reg))
              HandleVirtRegUse(MO_reg, MBB, MI);
          else if (!ReservedRegisters[MO_reg])
              HandlePhysRegUse(MO_reg, MI);
      }


      // Process all masked registers. (Call clobbers).
      for (unsigned i = 0, e = RegMasks.size(); i != e; ++i)
        HandleRegMask(MI->getOperand(RegMasks[i]));

      // MISSING: For all defined registers (both virtual and physical), update liveness using HandlePhysRegDef and HandleVirtRegDef.
      // Process all defs.
      for (unsigned i = 0; i < DefRegs.size(); ++i) {
          unsigned MO_reg = DefRegs[i];
          if (TargetRegisterInfo::isVirtualRegister(MO_reg))
              HandleVirtRegDef(MO_reg, MI);
          else if (!ReservedRegisters[MO_reg])
              HandlePhysRegDef(MO_reg, MI, Defs);
      }

      UpdatePhysRegDefs(MI, Defs);
    }

    // Handle any virtual assignments from PHI nodes which might be at the
    // bottom of this basic block.  We check all of our successor blocks to see
    // if they have PHI nodes, and if so, we simulate an assignment at the end
    // of the current block.
    if (!PHIVarInfo[MBB->getNumber()].empty()) {
      SmallVector<unsigned, 4>& VarInfoVec = PHIVarInfo[MBB->getNumber()];

      for (SmallVector<unsigned, 4>::iterator I = VarInfoVec.begin(),
             E = VarInfoVec.end(); I != E; ++I)
        // Mark it alive only in the block we are representing.
        MarkVirtRegAliveInBlock(getVarInfo(*I),MRI->getVRegDef(*I)->getParent(),
                                MBB);
    }

    // Finally, if the last instruction in the block is a return, make sure to
    // mark it as using all of the live-out values in the function.
    // Things marked both call and return are tail calls; do not do this for
    // them.  The tail callee need not take the same registers as input
    // that it produces as output, and there are dependencies for its input
    // registers elsewhere.
    if (!MBB->empty() && MBB->back().isReturn()
        && !MBB->back().isCall()) {
      MachineInstr *Ret = &MBB->back();

      for (MachineRegisterInfo::liveout_iterator
           I = MF->getRegInfo().liveout_begin(),
           E = MF->getRegInfo().liveout_end(); I != E; ++I) {
        assert(TargetRegisterInfo::isPhysicalRegister(*I) &&
               "Cannot have a live-out virtual register!");
        HandlePhysRegUse(*I, Ret);

        // Add live-out registers as implicit uses.
        if (!Ret->readsRegister(*I))
          Ret->addOperand(MachineOperand::CreateReg(*I, false, true));
      }
    }

    // MachineCSE may CSE instructions which write to non-allocatable physical
    // registers across MBBs. Remember if any reserved register is liveout.
    SmallSet<unsigned, 4> LiveOuts;
    for (MachineBasicBlock::const_succ_iterator SI = MBB->succ_begin(),
           SE = MBB->succ_end(); SI != SE; ++SI) {
      MachineBasicBlock *SuccMBB = *SI;
      if (SuccMBB->isLandingPad())
        continue;
      for (MachineBasicBlock::livein_iterator LI = SuccMBB->livein_begin(),
             LE = SuccMBB->livein_end(); LI != LE; ++LI) {
        unsigned LReg = *LI;
        if (!TRI->isInAllocatableClass(LReg))
          // Ignore other live-ins, e.g. those that are live into landing pads.
          LiveOuts.insert(LReg);
      }
    }

    // Loop over PhysRegDef / PhysRegUse, killing any registers that are
    // available at the end of the basic block.
    for (unsigned i = 0; i != NumRegs; ++i)
      if ((PhysRegDef[i] || PhysRegUse[i]) && !LiveOuts.count(i))
        HandlePhysRegDef(i, 0, Defs);

    std::fill(PhysRegDef,  PhysRegDef  + NumRegs, (MachineInstr*)0);
    std::fill(PhysRegUse,  PhysRegUse  + NumRegs, (MachineInstr*)0);
  }//end of the dfs of basic blocks

  // Convert and transfer the dead / killed information we have gathered into
  // VirtRegInfo onto MI's.
  for (unsigned i = 0, e1 = VirtRegInfo.size(); i != e1; ++i) {
    const unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
    for (unsigned j = 0, e2 = VirtRegInfo[Reg].Kills.size(); j != e2; ++j)
      if (VirtRegInfo[Reg].Kills[j] == MRI->getVRegDef(Reg))
        VirtRegInfo[Reg].Kills[j]->addRegisterDead(Reg, TRI);
      else
        VirtRegInfo[Reg].Kills[j]->addRegisterKilled(Reg, TRI);
  }

  // Check to make sure there are no unreachable blocks in the MC CFG for the
  // function.  If so, it is due to a bug in the instruction selector or some
  // other part of the code generator if this happens.
#ifndef NDEBUG
  for(MachineFunction::iterator i = MF->begin(), e = MF->end(); i != e; ++i)
    assert(Visited.count(&*i) != 0 && "unreachable basic block found");
#endif

  // TESTING

 // TEST



  MachineBasicBlock *Enter = MF->begin();

    for (MachineBasicBlock::iterator I = Enter->begin(), E = Enter->end();
         I != E; ++I) {
      MachineInstr *MI = I;
      unsigned NumOperandsToProcess = MI->getNumOperands();
      for (unsigned i = 0; i != NumOperandsToProcess; ++i) {
        MachineOperand &MO = MI->getOperand(i);
	if(MO.isReg() && TargetRegisterInfo::isVirtualRegister(MO.getReg()) ) {
	  errs()<<"Operand: ";
	  MO.print(errs());
	  errs()<<"\n";
	  errs()<<"Register number: "<<MO.getReg()<<"\n";
	  VarInfo& VRInfo = getVarInfo(MO.getReg());
	  VRInfo.dump();

	}
      }
    }


  delete[] PhysRegDef;
  delete[] PhysRegUse;
  delete[] PHIVarInfo;

  return false;
}

/// replaceKillInstruction - Update register kill info by replacing a kill
/// instruction with a new one.
void LiveVariables::replaceKillInstruction(unsigned Reg, MachineInstr *OldMI,
                                           MachineInstr *NewMI) {
  VarInfo &VI = getVarInfo(Reg);
  std::replace(VI.Kills.begin(), VI.Kills.end(), OldMI, NewMI);
}

/// removeVirtualRegistersKilled - Remove all killed info for the specified
/// instruction.
void LiveVariables::removeVirtualRegistersKilled(MachineInstr *MI) {

  // MISSING: Update MI so that it kills none of its operands.
    for (unsigned i = 0; i < MI->getNumOperands(); i++){
        MachineOperand MO = MI->getOperand(i);
        if (MO.isReg() && MO.isKill()){
            unsigned reg = MO.getReg();
            if (TargetRegisterInfo::isVirtualRegister(reg)){
                getVarInfo(reg).removeKill(MI);
            }
        }
    }

}

/// analyzePHINodes - Gather information about the PHI nodes in here. In
/// particular, we want to map the variable information of a virtual register
/// which is used in a PHI node. We map that to the BB the vreg is coming from.
///
void LiveVariables::analyzePHINodes(const MachineFunction& Fn) {
  for (MachineFunction::const_iterator I = Fn.begin(), E = Fn.end();
       I != E; ++I)
    for (MachineBasicBlock::const_iterator BBI = I->begin(), BBE = I->end();
         BBI != BBE && BBI->isPHI(); ++BBI)
      for (unsigned i = 1, e = BBI->getNumOperands(); i != e; i += 2)
        if (BBI->getOperand(i).readsReg())
          PHIVarInfo[BBI->getOperand(i + 1).getMBB()->getNumber()]
            .push_back(BBI->getOperand(i).getReg());
}

bool LiveVariables::VarInfo::isLiveIn(const MachineBasicBlock &MBB,
                                      unsigned Reg,
                                      MachineRegisterInfo &MRI) {

  // MISSING: Return true iff Reg is live at the start of MBB
    //1.get in and get out
    //2.get in but killed
    //3.defined inside and get out
    //4.defined inside and killed

    //1.
    if (AliveBlocks.test(MBB.getNumber()))
        return true;
    //3.4.
    MachineInstr *define = MRI.getVRegDef(Reg);
    if (define && define->getParent() == &MBB){
        return false;
    }
    //2.
    if (findKill(&MBB))
        return true;
}

bool LiveVariables::isLiveOut(unsigned Reg, const MachineBasicBlock &MBB) {

  // MISSING: Check whether Reg is alive after executing MBB.



  // Check to see if this value is live because there is a use in a successor
  // that kills it.

  // MISSING: Verify if there is a following basic block that uses the Reg and Kills it.
    LiveVariables::VarInfo &vi = getVarInfo(Reg);
    for (MachineBasicBlock::const_succ_iterator si = MBB.succ_begin(); 
            si != MBB.succ_end(); ++si){
        MachineBasicBlock * succ_mbb = *si;
        if (vi.AliveBlocks.test(succ_mbb->getNumber())){
            return true;
        }
        for (unsigned i = 0; i < vi.Kills.size(); i++){
            if (vi.Kills[i]->getParent() == succ_mbb){
                return true;
            }
        }

    }


  return false;
}

/// addNewBlock - Add a new basic block BB as an empty succcessor to DomBB. All
/// variables that are live out of DomBB will be marked as passing live through
/// BB.
void LiveVariables::addNewBlock(MachineBasicBlock *BB,
                                MachineBasicBlock *DomBB,
                                MachineBasicBlock *SuccBB) {
  const unsigned NumNew = BB->getNumber();

  // All registers used by PHI nodes in SuccBB must be live through BB.
  for (MachineBasicBlock::iterator BBI = SuccBB->begin(),
         BBE = SuccBB->end(); BBI != BBE && BBI->isPHI(); ++BBI)
    for (unsigned i = 1, e = BBI->getNumOperands(); i != e; i += 2)
      if (BBI->getOperand(i+1).getMBB() == BB)
        getVarInfo(BBI->getOperand(i).getReg()).AliveBlocks.set(NumNew);

  // Update info for all live variables
  for (unsigned i = 0, e = MRI->getNumVirtRegs(); i != e; ++i) {
    unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
    VarInfo &VI = getVarInfo(Reg);
    if (!VI.AliveBlocks.test(NumNew) && VI.isLiveIn(*SuccBB, Reg, *MRI))
      VI.AliveBlocks.set(NumNew);
  }
}
