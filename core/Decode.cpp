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
        num_to_decode_(p->num_to_decode)
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
            ILOG("Received: " << i);
        }
        if (uop_queue_credits_ > 0) {
            ev_decode_insts_event_.schedule(sparta::Clock::Cycle(0));
        }
    }

    // Handle incoming flush
    void Decode::handleFlush_(const FlushManager::FlushingCriteria & criteria)
    {
        ILOG("Got a flush call for " << criteria);
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
                fetch_queue_.pop();

                ILOG("Decoded: " << inst);

                inst->setStatus(Inst::Status::DECODED);
                insts->emplace_back(inst);
            }

            if (try_merge_insts_)
                insts = Decode::tryMergeInsts(insts);

            // Send decoded instructions to rename
            uop_queue_outp_.send(insts);

            // Decrement internal Uop Queue credits
            uop_queue_credits_ -= num_decode;

            // Send credits back to Fetch to get more instructions
            fetch_queue_credits_outp_.send(num_decode);
        }

        // If we still have credits to send instructions as well as
        // instructions in the queue, schedule another decode session
        if(uop_queue_credits_ > 0 && fetch_queue_.size() > 0) {
            ev_decode_insts_event_.schedule(1);
        }
    }

    // check inst pair can be merge
    InstPtr Decode::canMerge(InstPtr a, InstPtr b) {

        // Load Effective Address
        if (a->getMnemonic() == "slli" && b->getMnemonic() == "add" && 
            (a->getDestRegisterBitMask(core_types::RF_INTEGER) & b->getSrcRegisterBitMask(core_types::RF_INTEGER)) != 0) {
            
            return b;
        }


        // Index Load
        if (a->getMnemonic() == "add" && b->getMnemonic() == "ld" && 
            (a->getDestRegisterBitMask(core_types::RF_INTEGER) & b->getSrcRegisterBitMask(core_types::RF_INTEGER))!= 0) {
            
            return b;
        }


        // Clear Upper Word
        if (a->getMnemonic() == "slli" && b->getMnemonic() == "srli" && 
            (a->getDestRegisterBitMask(core_types::RF_INTEGER) & b->getSrcRegisterBitMask(core_types::RF_INTEGER)) != 0 &&
            a->getImmediate() == 32 && b->getImmediate() == 32) {
            
            return b;
        }

        return nullptr;
    }

    InstGroupPtr Decode::tryMergeInsts(InstGroupPtr insts) {

        std::deque<InstPtr> mergeQueue(insts->begin(), insts->end());
        InstGroupPtr newInsts = sparta::allocate_sparta_shared_pointer<InstGroup>(instgroup_allocator);

        while(mergeQueue.size()) {
            if (mergeQueue.size() == 1) {

                InstPtr a = mergeQueue.front();
                mergeQueue.pop_front();

                newInsts->emplace_back(a);
            }
            else {
                InstPtr a = mergeQueue.front();
                mergeQueue.pop_front();
                InstPtr b = mergeQueue.front();
                mergeQueue.pop_front();

                InstPtr mergedInst = Decode::canMerge(a, b);

                if (mergedInst == nullptr) {
                    newInsts->emplace_back(a);
                    mergeQueue.push_front(b);
                }
                else {
                    newInsts->emplace_back(mergedInst);
                }
            }
        }

        return newInsts;
    }

}
