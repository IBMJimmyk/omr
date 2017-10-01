/*******************************************************************************
 * Copyright (c) 2017, 2017 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at http://eclipse.org/legal/epl-2.0
 * or the Apache License, Version 2.0 which accompanies this distribution
 * and is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the
 * Eclipse Public License, v. 2.0 are satisfied: GNU General Public License,
 * version 2 with the GNU Classpath Exception [1] and GNU General Public
 * License, version 2 with the OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0
 *******************************************************************************/

#include "codegen/CodeGenerator.hpp"                  // for CodeGenerator, etc
#include "codegen/MemoryReference.hpp"
#include "codegen/RegisterPair.hpp"                   // for RegisterPair
#include "codegen/TreeEvaluator.hpp"
#include "il/ILOpCodes.hpp"                           // for ILOpCodes, etc
#include "il/ILOps.hpp"                               // for ILOpCode
#include "il/Node.hpp"                                // for Node, etc
#include "il/Node_inlines.hpp"
#include "infra/Assert.hpp"                           // for TR_ASSERT
#include "x/codegen/X86Instruction.hpp"
#include "x/codegen/X86Ops.hpp"                       // for ::LABEL, ::JE4, etc

namespace TR { class Instruction; }

static TR::MemoryReference* ConvertToPatchableMemoryReference(TR::MemoryReference* mr, TR::Node* node, TR::CodeGenerator* cg)
   {
   if (mr->getSymbolReference().isUnresolved())
      {
      // The load instructions may be wider than 8-bytes (our patching window)
      // but we won't know that for sure until after register assignment.
      // Hence, the unresolved memory reference must be evaluated into a register first.
      //
      TR::Register* tempReg = cg->allocateRegister();
      generateRegMemInstruction(LEARegMem(cg), node, tempReg, mr, cg);
      mr = generateX86MemoryReference(tempReg, 0, cg);
      cg->stopUsingRegister(tempReg);
      }
   return mr;
   }

TR::Register* OMR::X86::TreeEvaluator::SIMDRegLoadEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   TR::Register* globalReg = node->getRegister();
   if (!globalReg)
      {
      globalReg = cg->allocateRegister(TR_VRF);
      node->setRegister(globalReg);
      }
   return globalReg;
   }

TR::Register* OMR::X86::TreeEvaluator::SIMDRegStoreEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   TR::Node* child = node->getFirstChild();
   TR::Register* globalReg = cg->evaluate(child);
   cg->machine()->setXMMGlobalRegister(node->getGlobalRegisterNumber() - cg->machine()->getNumGlobalGPRs(), globalReg);
   cg->decReferenceCount(child);
   return globalReg;
   }

TR::Register* OMR::X86::TreeEvaluator::SIMDloadEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   TR::MemoryReference* tempMR = generateX86MemoryReference(node, cg);
   tempMR = ConvertToPatchableMemoryReference(tempMR, node, cg);
   TR::Register* resultReg = cg->allocateRegister(TR_VRF);

   TR_X86OpCodes opCode = BADIA32Op;
   switch (node->getSize())
      {
      case 16: //TODO: the node is set to size 16 but it should be 32 due to 256 bit vectors
         opCode = MOVDQU256RegMem;
         break;
      default:
         if (cg->comp()->getOption(TR_TraceCG))
            traceMsg(cg->comp(), "Unsupported fill size: Node = %p\n", node);
         TR_ASSERT(false, "Unsupported fill size");
         break;
      }

   TR::Instruction* instr = generateRegMemInstruction(opCode, node, resultReg, tempMR, cg);
   if (node->getOpCode().isIndirect())
      cg->setImplicitExceptionPoint(instr);
   node->setRegister(resultReg);
   tempMR->decNodeReferenceCounts(cg);
   return resultReg;
   }

TR::Register* OMR::X86::TreeEvaluator::SIMDstoreEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   TR::Node* valueNode = node->getChild(node->getOpCode().isIndirect() ? 1 : 0);
   TR::MemoryReference* tempMR = generateX86MemoryReference(node, cg);
   tempMR = ConvertToPatchableMemoryReference(tempMR, node, cg);
   TR::Register* valueReg = cg->evaluate(valueNode);

   TR_X86OpCodes opCode = BADIA32Op;
   switch (node->getSize())
      {
      case 16: //TODO: the node is set to size 16 but it should be 32 due to 256 bit vectors
         opCode = MOVDQU256MemReg;
         break;
      default:
         if (cg->comp()->getOption(TR_TraceCG))
            traceMsg(cg->comp(), "Unsupported fill size: Node = %p\n", node);
         TR_ASSERT(false, "Unsupported fill size");
         break;
      }

   TR::Instruction* instr = generateMemRegInstruction(opCode, node, tempMR, valueReg, cg);

   cg->decReferenceCount(valueNode);
   tempMR->decNodeReferenceCounts(cg);
   if (node->getOpCode().isIndirect())
      cg->setImplicitExceptionPoint(instr);
   return NULL;
   }

//TODO: reminder that VPERMQ is an AVX2 instruction
TR::Register* OMR::X86::TreeEvaluator::SIMDsplatsEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   TR::Node* childNode = node->getChild(0);
   TR::Register* childReg = cg->evaluate(childNode);

   TR::Register* resultReg = cg->allocateRegister(TR_VRF);
   switch (node->getDataType())
      {
      case TR::VectorInt32:
         generateRegRegInstruction(MOVDRegReg4, node, resultReg, childReg, cg);
         generateRegRegImmInstruction(PSHUFDRegRegImm1, node, resultReg, resultReg, 0x00, cg); // 00 00 00 00 shuffle xxxA to AAAA
         generateRegRegImmInstruction(VPERMQRegRegImm1, node, resultReg, resultReg, 0x00, cg); // permute xxxxxxAA to AAAAAAAA
         break;
      case TR::VectorInt64:
         if (TR::Compiler->target.is32Bit())
            {
            TR::Register* tempVectorReg = cg->allocateRegister(TR_VRF);
            generateRegRegInstruction(MOVDRegReg4, node, tempVectorReg, childReg->getHighOrder(), cg);
            generateRegImmInstruction(PSLLQRegImm1, node, tempVectorReg, 0x20, cg);
            generateRegRegInstruction(MOVDRegReg4, node, resultReg, childReg->getLowOrder(), cg);
            generateRegRegInstruction(PORRegReg, node, resultReg, tempVectorReg, cg);
            cg->stopUsingRegister(tempVectorReg);
            }
         else
            {
            generateRegRegInstruction(MOVQRegReg8, node, resultReg, childReg, cg);
            }
         generateRegRegImmInstruction(VPERMQRegRegImm1, node, resultReg, resultReg, 0x00, cg); // permute xxxxxxBA to BABABABA
         break;
      case TR::VectorFloat:
         generateRegRegImmInstruction(PSHUFDRegRegImm1, node, resultReg, childReg, 0x00, cg); // 00 00 00 00 shuffle xxxA to AAAA
         generateRegRegImmInstruction(VPERMQRegRegImm1, node, resultReg, resultReg, 0x00, cg); // permute xxxxxxAA to AAAAAAAA
         break;
      case TR::VectorDouble:
         generateRegRegImmInstruction(VPERMQRegRegImm1, node, resultReg, childReg, 0x00, cg); // 01 00 01 00 shuffle xxBA to BABA
         break;
      default:
         if (cg->comp()->getOption(TR_TraceCG))
            traceMsg(cg->comp(), "Unsupported data type, Node = %p\n", node);
         TR_ASSERT(false, "Unsupported data type");
         break;
      }

   node->setRegister(resultReg);
   cg->decReferenceCount(childNode);
   return resultReg;
   }

//TODO: reminder that VPERMQ is an AVX2 instruction
TR::Register* OMR::X86::TreeEvaluator::SIMDgetvelemEvaluator(TR::Node* node, TR::CodeGenerator* cg)
   {
   if (TR::Compiler->target.is32Bit())
      {
      TR_ASSERT(false, "256 bit vector getvelem unsupported under 32 bit\n");
      }
   TR::Node* firstChild = node->getChild(0);
   TR::Node* secondChild = node->getChild(1);

   TR::Register* srcVectorReg = cg->evaluate(firstChild);
   TR::Register* resReg = 0;
   TR::Register* lowResReg = 0;
   TR::Register* highResReg = 0;

   int32_t elementCount = -1;
   switch (firstChild->getDataType())
      {
      case TR::VectorInt8:
      case TR::VectorInt16:
         TR_ASSERT(false, "unsupported vector type %s in SIMDgetvelemEvaluator.\n", firstChild->getDataType().toString());
         break;
      case TR::VectorInt32:
         elementCount = 8;
         resReg = cg->allocateRegister();
         break;
      case TR::VectorInt64:
         elementCount = 4;
         /*if (TR::Compiler->target.is32Bit())
            {
            lowResReg = cg->allocateRegister();
            highResReg = cg->allocateRegister();
            resReg = cg->allocateRegisterPair(lowResReg, highResReg);
            }
         else
            {*/
            resReg = cg->allocateRegister();
            //}
         break;
      case TR::VectorFloat:
         elementCount = 8;
         resReg = cg->allocateSinglePrecisionRegister(TR_FPR);
         break;
      case TR::VectorDouble:
         elementCount = 4;
         resReg = cg->allocateRegister(TR_FPR);
         break;
      default:
         TR_ASSERT(false, "unrecognized vector type %s in SIMDgetvelemEvaluator.\n", firstChild->getDataType().toString());
      }

   if (secondChild->getOpCode().isLoadConst())
      {
      int32_t elem = secondChild->getInt();

      TR_ASSERT(elem >= 0 && elem < elementCount, "Element can only be 0 to %u\n", elementCount - 1);

      TR::Register* dstReg = 0;
      if (8 == elementCount)
         {
         /*
          * the value to be read (indicated by elem) from srcVectorReg is copied into the least significant bits
          * of dstReg. The other bits in dstReg should never be read.
          * for float, dstReg and resReg are the same because PSHUFD can work directly with TR_FPR registers
          * for Int32, the result needs to be moved from the dstReg to a TR_GPR resReg.
          */
         if (TR::VectorInt32 == firstChild->getDataType())
            {
            dstReg = cg->allocateRegister(TR_VRF);
            }
         else //TR::VectorFloat == firstChild->getDataType()
            {
            dstReg = resReg;
            }

         switch (elem)
            {
            case 0:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xff, cg); // permute Axxxxxxx to AxAxAxAx
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, dstReg, 0xff, cg);       // shuffle AxAxAxAx to AAAAAAAA
               break;
            case 1:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xff, cg); // permute xBxxxxxx to xBxBxBxB
               break;
            case 2:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xaa, cg); // permute xxCxxxxx to CxCxCxCx
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, dstReg, 0xff, cg);       // shuffle CxCxCxCx to CCCCCCCC
               break;
            case 3:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xaa, cg); // permute xxxDxxxx to xDxDxDxD
               break;
            case 4:
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, srcVectorReg, 0x03, cg); // shuffle xxxxExxx to xxxxxxxE
               break;
            case 5:
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, srcVectorReg, 0x02, cg); // shuffle xxxxxFxx to xxxxxxxF
               break;
            case 6:
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, srcVectorReg, 0x01, cg); // shuffle xxxxxxGx to xxxxxxxG
               break;
            case 7:
               generateRegRegInstruction(MOVDQURegReg, node, dstReg, srcVectorReg, cg); //register already contains xxxxxxxH so just mov to dstReg
               break;
            default:
               TR_ASSERT(false, "Element can only be 0 to %u\n", elementCount - 1);
               break;
            }

         if (TR::VectorInt32 == firstChild->getDataType())
            {
            generateRegRegInstruction(MOVDReg4Reg, node, resReg, dstReg, cg);
            cg->stopUsingRegister(dstReg);
            }
         }
      else //2 == elementCount
         {
         /*
          * for double, dstReg and resReg are the same because PSHUFD can work directly with TR_FPR registers
          * for Int64, the result needs to be moved from the dstReg to a TR_GPR resReg.
          */
         if (TR::VectorInt64 == firstChild->getDataType())
            {
            dstReg = cg->allocateRegister(TR_VRF);
            }
         else //TR::VectorDouble == firstChild->getDataType()
            {
            dstReg = resReg;
            }

         /*
          * the value to be read needs to be in the least significant 64 bits.
          */
         switch (elem)
            {
            case 0:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xff, cg); // permute ABxxxxxx to ABABABAB
               break;
            case 1:
               generateRegRegImmInstruction(VPERMQRegRegImm1, node, dstReg, srcVectorReg, 0xaa, cg); // permute xxCDxxxx to CDCDCDCD
               break;
            case 2:
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, srcVectorReg, 0x0e, cg); // shuffle xxxxEFxx to xxxxxxEF
               break;
            case 3:
               generateRegRegInstruction(MOVDQURegReg, node, dstReg, srcVectorReg, cg); //register already contains xxxxxxGH so just mov to dstReg
               break;
            default:
               TR_ASSERT(false, "Element can only be 0 to %u\n", elementCount - 1);
               break;
            }

         if (TR::VectorInt64 == firstChild->getDataType())
            {
            /*if (TR::Compiler->target.is32Bit())
               {
               generateRegRegInstruction(MOVDReg4Reg, node, lowResReg, dstReg, cg);
               generateRegRegImmInstruction(PSHUFDRegRegImm1, node, dstReg, srcVectorReg, (0 == elem) ? 0x03 : 0x01, cg);
               generateRegRegInstruction(MOVDReg4Reg, node, highResReg, dstReg, cg);
               }
            else
               {*/
               generateRegRegInstruction(MOVQReg8Reg, node, resReg, dstReg, cg);
               //}
            cg->stopUsingRegister(dstReg);
            }
         }
      }
   else
      {
      //TODO: handle non-constant second child case
      TR_ASSERT(false, "non-const second child not currently supported in SIMDgetvelemEvaluator.\n");
      }

   node->setRegister(resReg);
   cg->decReferenceCount(firstChild);
   cg->decReferenceCount(secondChild);

   return resReg;
   }

