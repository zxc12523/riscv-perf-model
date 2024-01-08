// <Decode.cpp> -*- C++ -*-


#include <algorithm>

#include "Decode.hpp"

#include "sparta/events/StartupEvent.hpp"
#include "sparta/utils/LogUtils.hpp"

namespace olympia
{
    constexpr char Decode::name[];

    Decode::Decode(sparta::TreeNode * node,
                   const DecodeParameterSet * p) :
        sparta::Unit(node),
        fetch_queue_("FetchQueue", p->fetch_queue_size, node->getClock(), &unit_stat_set_),
        num_to_decode_(p->num_to_decode), 
        fuse_insts_(p->fuse_insts), 
        fuse_mode_(p->fuse_mode)
    {
        fetch_queue_.enableCollection(node);

        fetch_queue_write_in_.
            registerConsumerHandler(CREATE_SPARTA_HANDLER_WITH_DATA(Decode, fetchBufferAppended_, InstGroupPtr));
        uop_queue_credits_in_.
            registerConsumerHandler(CREATE_SPARTA_HANDLER_WITH_DATA(Decode, receiveUopQueueCredits_, uint32_t));
        in_reorder_flush_.
            registerConsumerHandler(CREATE_SPARTA_HANDLER_WITH_DATA(Decode, handleFlush_, FlushManager::FlushingCriteria));

        sparta::StartupEvent(node, CREATE_SPARTA_HANDLER(Decode, sendInitialCredits_));
    }

    // Send fetch the initial credit count
    void Decode::sendInitialCredits_()
    {
        fetch_queue_credits_outp_.send(fetch_queue_.capacity());
    }

    // Receive Uop credits from Dispatch
    void Decode::receiveUopQueueCredits_(const uint32_t & credits) {
        uop_queue_credits_ += credits;
        if (fetch_queue_.size() > 0) {
            ev_decode_insts_event_.schedule(sparta::Clock::Cycle(0));
        }

        ILOG("Received credits: " << uop_queue_credits_in_);
    }

    // Called when the fetch buffer was appended by Fetch.  If decode
    // has the credits, then schedule a decode session.  Otherwise, go
    // to sleep
    void Decode::fetchBufferAppended_(const InstGroupPtr & insts)
    {
        // Cache the instructions in the instruction queue if we can't decode this cycle
        for(auto & i : *insts)
        {
            fetch_queue_.push(i);
            // ILOG("Received: " << i);
        }
        if (uop_queue_credits_ > 0) {
            ev_decode_insts_event_.schedule(sparta::Clock::Cycle(0));
        }
    }

    // Handle incoming flush
    void Decode::handleFlush_(const FlushManager::FlushingCriteria & criteria)
    {
        // ILOG("Got a flush call for " << criteria);
        fetch_queue_credits_outp_.send(fetch_queue_.size());
        fetch_queue_.clear();
    }

    // Decode instructions
    void Decode::decodeInsts_()
    {
        uint32_t num_decode = std::min(uop_queue_credits_, fetch_queue_.size());
        num_decode = std::min(num_decode, num_to_decode_);

        if(num_decode > 0)
        {
            InstGroupPtr insts =
                sparta::allocate_sparta_shared_pointer<InstGroup>(instgroup_allocator);
            // Send instructions on their way to rename
            for(uint32_t i = 0; i < num_decode; ++i) {
                const auto & inst = fetch_queue_.read(0);
                insts->emplace_back(inst);
                inst->setStatus(Inst::Status::RENAMED);

                ILOG("Decoded: " << inst);

                fetch_queue_.pop();
            }

            if (fuse_insts_)
                insts = Decode::tryFuseInsts(insts);

            // Send decoded instructions to rename
            uop_queue_outp_.send(insts);

            // Decrement internal Uop Queue credits
            uop_queue_credits_ -= insts->size();

            // Send credits back to Fetch to get more instructions
            fetch_queue_credits_outp_.send(num_decode);
        }

        // If we still have credits to send instructions as well as
        // instructions in the queue, schedule another decode session
        if(uop_queue_credits_ > 0 && fetch_queue_.size() > 0) {
            ev_decode_insts_event_.schedule(1);
        }
    }

    bool Decode::checkRegisterDependency(InstPtr FirstInst, InstPtr SecondInst) {
        return (FirstInst->getIntDestRegs() & SecondInst->getIntSourceRegs()) != 0;
    }

    bool Decode::checkRegisterSameSource(InstPtr FirstInst, InstPtr SecondInst) {
        return (FirstInst->getIntSourceRegs() & SecondInst->getIntSourceRegs()) != 0;
    }

    // Fuse SLLI/SLLIW followed by ADD/ADDW.
    // slli rd r1 imm
    // add rd, rd, rs2
    bool Decode::isLoadEffectAddress(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "slli" && 
            FirstInst->getMnemonic() != "slliw" && 
            FirstInst->getMnemonic() != "c.slli")
            return false;

        if (SecondInst->getMnemonic() != "add" && 
            SecondInst->getMnemonic() != "addw" &&
            SecondInst->getMnemonic() != "c.add") 
            return false;

        return checkRegisterDependency(FirstInst, SecondInst);
    }

    // Fuse load with add:
    // add rd, rs1, rs2
    // ld rd, 0(rd)
    bool Decode::isIndexLoad(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "add" && 
            FirstInst->getMnemonic() != "c.add")
            return false;
        
        if (SecondInst->getMnemonic() != "ld" && 
            SecondInst->getMnemonic() != "c.ld") 
            return false;
        
        return checkRegisterDependency(FirstInst, SecondInst);
    }

    // Fuse zero extension of word:
    // slli rd, rs1, 32
    // srli rd, rd, 32
    bool Decode::isClearUpperWord(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "slli" && 
            FirstInst->getMnemonic() != "c.slli")
            return false; 

        if (SecondInst->getMnemonic() != "srli" && 
            SecondInst->getMnemonic() != "c.srli")
            return false; 
        
        if (FirstInst->getImmediate() != 32 && 
            SecondInst->getImmediate() != 32)
            return false;
        
        return checkRegisterDependency(FirstInst, SecondInst);
    }

    // Fuse LUI followed by ADDI or ADDIW.
    // rd = imm[31:0] which decomposes to
    // lui rd, imm[31:12]
    // addi(w) rd, rd, imm[11:0]
    bool Decode::isLoadImmediateIdiom(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "lui" && 
            FirstInst->getMnemonic() != "c.lui")
            return false;

        if (SecondInst->getMnemonic() != "addi" && 
            SecondInst->getMnemonic() != "addiw" && 
            SecondInst->getMnemonic() != "c.addi")
            return false;

        return checkRegisterDependency(FirstInst, SecondInst);
    }


    // Fuse AUIPC followed by ADDI
    // auipc rd, imm20
    // addi rd, rd, imm12
    bool Decode::isLoadGloabal(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "auipc") 
            return false;
        
        if (SecondInst->getMnemonic() != "ld" && 
            SecondInst->getMnemonic() != "addi") 
            return false;
        
        return checkRegisterDependency(FirstInst, SecondInst);
    }


    // Fuse consecutive load
    // lw rd, r1, imm
    // lw rd, r1, imm + 4
    bool Decode::isLoadPair32bits(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "lw" && 
            FirstInst->getMnemonic() != "c.lw" && 
            FirstInst->getMnemonic() != "c.lwsp")
            return false;

        if (SecondInst->getMnemonic() != "lw" && 
            SecondInst->getMnemonic() != "c.lw" && 
            SecondInst->getMnemonic() != "c.lwsp")
            return false;
        
        if (abs((long)FirstInst->getImmediate() - (long)SecondInst->getImmediate()) != 4)
            return false;
        
        return checkRegisterSameSource(FirstInst, SecondInst);
    }


    // Fuse consecutive load
    // ld rd, r1, imm
    // ld rd, r1, imm + 8
    bool Decode::isLoadPair64bits(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "ld" && 
            FirstInst->getMnemonic() != "c.ld" && 
            FirstInst->getMnemonic() != "c.ldsp")
            return false;

        if (SecondInst->getMnemonic() != "ld" && 
            SecondInst->getMnemonic() != "c.ld" && 
            SecondInst->getMnemonic() != "c.ldsp")
            return false;
        
        if (abs((long)FirstInst->getImmediate() - (long)SecondInst->getImmediate()) != 8)
            return false;
        
        return checkRegisterSameSource(FirstInst, SecondInst);
    }


    // Fuse consecutive store
    // sw rd, r1, imm
    // sw rd, r1, imm + 4
    bool Decode::isStorePair32bits(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "sw" && 
            FirstInst->getMnemonic() != "c.sw" && 
            FirstInst->getMnemonic() != "c.swsp")
            return false;

        if (SecondInst->getMnemonic() != "sw" && 
            SecondInst->getMnemonic() != "c.sw" && 
            SecondInst->getMnemonic() != "c.swsp")
            return false;
        
        if (abs((long)FirstInst->getImmediate() - (long)SecondInst->getImmediate()) != 4)
            return false;
        
        return checkRegisterSameSource(FirstInst, SecondInst);
    }


    // Fuse consecutive store
    // sd rd, r1, imm
    // sd rd, r1, imm + 8
    bool Decode::isStorePair64bits(InstPtr FirstInst, InstPtr SecondInst) {
        if (FirstInst->getMnemonic() != "sd" && 
            FirstInst->getMnemonic() != "c.sd" && 
            FirstInst->getMnemonic() != "c.sdsp")
            return false;

        if (SecondInst->getMnemonic() != "sd" && 
            SecondInst->getMnemonic() != "c.sd" && 
            SecondInst->getMnemonic() != "c.sdsp")
            return false;
        
        if (abs((long)FirstInst->getImmediate() - (long)SecondInst->getImmediate()) != 8)
            return false;
        
        return checkRegisterSameSource(FirstInst, SecondInst);
    }


    // Fuse shxadd followed by load
    // sh3add rd, r1, r2
    // ld rd, rd, 0
    bool Decode::isShxaddLoad(InstPtr FirstInst, InstPtr SecondInst) {
        if (!(FirstInst->getMnemonic() == "sh1add" && SecondInst->getMnemonic() == "lh") && 
            !(FirstInst->getMnemonic() == "sh2add" && SecondInst->getMnemonic() == "lw") && 
            !(FirstInst->getMnemonic() == "sh3add" && SecondInst->getMnemonic() == "ld"))
            return false;
        
        return checkRegisterDependency(FirstInst, SecondInst);
    }

    // Fuse addi/li followed by branch
    // addi rd, r1, imm
    // c.beqz / c.beqz rd imm
    bool Decode::isCompareImmediate(InstPtr FirstInst, InstPtr SecondInst) {
        if (!(FirstInst->getMnemonic() == "c.addi"  && SecondInst->getMnemonic() == "c.beqz") ||
            !(FirstInst->getMnemonic() == "c.addi"  && SecondInst->getMnemonic() == "c.bnez") || 
            !(FirstInst->getMnemonic() == "c.addiw" && SecondInst->getMnemonic() == "c.beqz") || 
            !(FirstInst->getMnemonic() == "c.addiw" && SecondInst->getMnemonic() == "c.bnez") || 
            !(FirstInst->getMnemonic() == "c.li"    && SecondInst->getMnemonic() == "bne")    || 
            !(FirstInst->getMnemonic() == "c.li"    && SecondInst->getMnemonic() == "beq")) 
            return false;
        

        return checkRegisterDependency(FirstInst, SecondInst);
    }

    // check inst pair can be fuse
    InstPtr Decode::tryFuse(InstPtr a, InstPtr b) {

        // Load Effective Address
        if (isLoadEffectAddress(a, b)) {
            ILOG("Load Effective Address: " << a << b);
            b->setCompressed(Inst::Compressed::Load_Effective_Address);
            return b;
        }

        // Index Load
        if (isIndexLoad(a, b)) {
            ILOG("Index Load: " << a << b);
            b->setCompressed(Inst::Compressed::Index_Load);
            return b;
        }


        // Clear Upper Word
        if (isClearUpperWord(a, b)) {
            ILOG("Clear Upper Word: " << a << b);
            b->setCompressed(Inst::Compressed::Clear_Upper_Word);
            return b;
        }

        // Load Immediate Idiom
        if (isLoadImmediateIdiom(a, b)) {
            ILOG("Load Immediate Idiom: " << a << b);
            b->setCompressed(Inst::Compressed::Load_Immediate_Idiom);
            return b;
        }

        // Load Global
        if (isLoadGloabal(a, b)) {
            ILOG("Load Global: " << a << b);
            b->setCompressed(Inst::Compressed::Load_Global);
            return b;
        }

        // Load Pair 32bits
        if (isLoadPair32bits(a, b)) {
            ILOG("Load pair: " << a << b);
            b->setCompressed(Inst::Compressed::Load_Pair);
            return b;
        }

        // Load Pair 64bits
        if (isLoadPair64bits(a, b)) {
            ILOG("Load pair: " << a << b);
            b->setCompressed(Inst::Compressed::Load_Pair);
            return b;
        }

        // Store Pair 32bits
        if (isStorePair32bits(a, b)) {
            ILOG("Store pair: " << a << b);
            b->setCompressed(Inst::Compressed::Store_Pair);
            return b;
        }

        // Store Pair 64bits
        if (isStorePair64bits(a, b)) {
            ILOG("Store pair: " << a << b);
            b->setCompressed(Inst::Compressed::Store_Pair);
            return b;
        }

        // Shift Load Pair
        if (isShxaddLoad(a, b)) {
            ILOG("shift + load" << a << b);
            b->setCompressed(Inst::Compressed::Shift_Load);
            return b;
        }

        if (isCompareImmediate(a, b)) {
            ILOG("Imm + Cmp");
            b->setCompressed(Inst::Compressed::Imm_Cmp);
            return b;
        }

        return nullptr;
    }

    InstGroupPtr Decode::tryFuseInsts(InstGroupPtr insts) {

        std::vector<InstPtr> fuseVector(insts->begin(), insts->end());

        InstGroupPtr newInsts = sparta::allocate_sparta_shared_pointer<InstGroup>(instgroup_allocator);

        if (fuse_mode_ == 0) {
            for (long unsigned int i = 0; i < fuseVector.size(); i++) {
                if (fuseVector[i]->getCompressed() || (i == fuseVector.size() - 1)) {
                    newInsts->emplace_back(fuseVector[i]);
                    continue;
                }

                InstPtr fusedInst = Decode::tryFuse(fuseVector[i], fuseVector[i+1]);

                if (fusedInst != nullptr) {
                    fuseVector[i+1] = fusedInst;
                }
                else {
                    newInsts->emplace_back(fuseVector[i]);
                }
            }
        }
        else
        {
            for(long unsigned int i = 0; i < fuseVector.size(); i++) {
                int fused = 0;

                for(long unsigned int j=i+1;j<fuseVector.size();j++) {
                    if (fuseVector[j]->getCompressed() != 0) {
                        break;
                    }

                    InstPtr fusedInst = Decode::tryFuse(fuseVector[i], fuseVector[j]);

                    if (fusedInst != nullptr) {
                        fuseVector[j] = fusedInst;
                        fused = 1;
                        break;
                    }
                    else if (fuseVector[i]->getIntDestRegs() == fuseVector[j]->getIntDestRegs()) {
                        break;
                    }
                }

                if (!fused) {
                    newInsts->emplace_back(fuseVector[i]);
                }
            }
        }

        return newInsts;
    }

}
