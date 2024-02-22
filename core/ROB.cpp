// <ROB.cpp> -*- C++ -*-


#include <algorithm>
#include "ROB.hpp"

#include "sparta/utils/LogUtils.hpp"
#include "sparta/events/StartupEvent.hpp"

namespace olympia
{
    const char ROB::name[] = "rob";

    ROB::ROB(sparta::TreeNode * node,
             const ROBParameterSet * p) :
        sparta::Unit(node),
        stat_ipc_(&unit_stat_set_,
                  "ipc",
                  "Instructions retired per cycle",
                  &unit_stat_set_,
                  "total_number_retired/cycles"),
        num_retired_(&unit_stat_set_,
                     "total_number_retired",
                     "The total number of instructions retired by this core",
                     sparta::Counter::COUNT_NORMAL),
        num_flushes_(&unit_stat_set_,
                     "total_number_of_flushes",
                     "The total number of flushes performed by the ROB",
                     sparta::Counter::COUNT_NORMAL),
        num_arith_(&unit_stat_set_,
                     "total_number_of_arithmatic",
                     "The total number of flushes performed by the ROB",
                     sparta::Counter::COUNT_NORMAL),
        num_branch_(&unit_stat_set_,
                     "total_number_of_branch",
                     "The total number of flushes performed by the ROB",
                     sparta::Counter::COUNT_NORMAL),
        num_load_(&unit_stat_set_,
                     "total_number_of_load",
                     "The total number of flushes performed by the ROB",
                     sparta::Counter::COUNT_NORMAL),
        num_store_(&unit_stat_set_,
                     "total_number_of_store",
                     "The total number of flushes performed by the ROB",
                     sparta::Counter::COUNT_NORMAL),
        overall_ipc_si_(&stat_ipc_),
        period_ipc_si_(&stat_ipc_),
        retire_timeout_interval_(p->retire_timeout_interval),
        num_to_retire_(p->num_to_retire),
        num_insts_to_retire_(p->num_insts_to_retire),
        retire_heartbeat_(p->retire_heartbeat),
        reorder_buffer_("ReorderBuffer", p->retire_queue_depth,
                        node->getClock(), &unit_stat_set_)
    {
        // Set a cycle delay on the retire, just for kicks
        ev_retire_.setDelay(1);

        // Set up the reorder buffer to support pipeline collection.
        reorder_buffer_.enableCollection(node);

        in_reorder_buffer_write_.
            registerConsumerHandler(CREATE_SPARTA_HANDLER_WITH_DATA(ROB, robAppended_, InstGroup));

        in_reorder_flush_.
            registerConsumerHandler(CREATE_SPARTA_HANDLER_WITH_DATA(ROB, handleFlush_,
                                                                  FlushManager::FlushingCriteria));

        // Do not allow this event to keep simulation alive
        ev_ensure_forward_progress_.setContinuing(false);

        // Notify other components when ROB stops the simulation
        rob_drained_notif_source_.reset(new sparta::NotificationSource<bool>(
            this->getContainer(),
            "rob_notif_channel",
            "Notification channel for rob",
            "rob_notif_channel"
        ));
        // Send initial credits to anyone that cares.  Probably Dispatch.
        sparta::StartupEvent(node, CREATE_SPARTA_HANDLER(ROB, sendInitialCredits_));

        num_compress_.resize(10, 0);
    }

    /// Destroy!
    ROB::~ROB() {
        // Logging can be done from destructors in the correct simulator setup
        ILOG("ROB is destructing now, but you can still see this message");
    }

    void ROB::sendInitialCredits_()
    {
        out_reorder_buffer_credits_.send(reorder_buffer_.capacity());
        ev_ensure_forward_progress_.schedule(retire_timeout_interval_);
    }

    void ROB::retireEvent_() {
        retireInstructions_();
    }

    // An illustration of the use of the callback -- instead of
    // getting a reference, you can pull the data from the port
    // directly, albeit inefficient and superfluous here...
    void ROB::robAppended_(const InstGroup &) {
        for(auto & i : *in_reorder_buffer_write_.pullData()) {
            reorder_buffer_.push(i);
            ILOG("retire appended: " << i);
        }

        ev_retire_.schedule(sparta::Clock::Cycle(0));
    }

    void ROB::handleFlush_(const FlushManager::FlushingCriteria &)
    {
        // Clean up internals and send new credit count
        out_reorder_buffer_credits_.send(reorder_buffer_.size());
        reorder_buffer_.clear();
    }

    void ROB::retireInstructions_()
    {
        const uint32_t num_to_retire = std::min(reorder_buffer_.size(), num_to_retire_);

        ILOG("num to retire: " << num_to_retire);

        uint32_t retired_this_cycle = 0;
        for(uint32_t i = 0; i < num_to_retire; ++i)
        {
            auto ex_inst_ptr = reorder_buffer_.access(0);
            sparta_assert(nullptr != ex_inst_ptr);
            auto & ex_inst = *ex_inst_ptr;
            sparta_assert(ex_inst.isSpeculative() == false,
                          "Uh, oh!  A speculative instruction is being retired: " << ex_inst);
            if(ex_inst.getStatus() == Inst::Status::COMPLETED)
            {
                // UPDATE:
                ex_inst.setStatus(Inst::Status::RETIRED);
                if (ex_inst.isStoreInst()) {
                    out_rob_retire_ack_.send(ex_inst_ptr);
                }
                // sending retired instruction to rename
                out_rob_retire_ack_rename_.send(ex_inst_ptr);

                if (ex_inst_ptr->getCompressed()) {
                    num_retired_ += 2;
                }
                else {
                    num_retired_ += 1;
                }

                ++retired_this_cycle;
                ++num_compress_[ex_inst_ptr->getCompressed()];
                reorder_buffer_.pop();

                num_arith_ += ex_inst_ptr->isArith();
                num_branch_ += ex_inst_ptr->isBranch();
                num_load_ += ex_inst_ptr->isLoad();
                num_store_ += ex_inst_ptr->isStoreInst();

                ILOG("retiring " << ex_inst);

                if(SPARTA_EXPECT_FALSE((num_retired_ >= retire_heartbeat_))) {
                    std::cout << "olympia: Retired " << num_retired_.get()
                              << " instructions in " << getClock()->currentCycle()
                              << " cycles.  Period IPC: " << period_ipc_si_.getValue()
                              << " overall IPC: " << overall_ipc_si_.getValue()
                              << std::endl;
                    std::cout << "-------------------- Statistic information --------------------" << std::endl;
                    std::cout << "Arith:                " << num_arith_     << std::endl
                              << "Branch:               " << num_branch_    << std::endl
                              << "Load:                 " << num_load_      << std::endl
                              << "Store:                " << num_store_     << std::endl
                              << std::endl;
                    std::cout << "-------------------- Statistic information --------------------" << std::endl;
                    std::cout << "-------------------- Compression information --------------------" << std::endl;
                    for (auto i : num_compress_) {
                        std::cerr << i << ' ';
                    }
                    std::cerr << '\n';

                    // std::cerr << "None:                     " << num_compress_[0] << std::endl
                    //           << "Load_Effective_Address:   " << num_compress_[1] << std::endl
                    //           << "Index_Load:               " << num_compress_[2] << std::endl
                    //           << "Clear_Upper_Word:         " << num_compress_[3] << std::endl
                    //           << "Load_Immediate_Idiom:     " << num_compress_[4] << std::endl
                    //           << "Load_Global:              " << num_compress_[5] << std::endl
                    //           << "Load_Pair:                " << num_compress_[6] << std::endl
                    //           << "Store_Pair:               " << num_compress_[7] << std::endl
                    //           << "Shift_Load_Pair:          " << num_compress_[8] << std::endl
                    //           << "Imm_Cmp:                  " << num_compress_[9] << std::endl
                    //           << std::endl;
                    std::cout << "-------------------- Compression information --------------------" << std::endl;
                    period_ipc_si_.start();
                }
                // Will be true if the user provides a -i option
                if (SPARTA_EXPECT_FALSE((num_retired_ >= num_insts_to_retire_))) {
                    rob_stopped_simulation_ = true;
                    rob_drained_notif_source_->postNotification(true);
                    getScheduler()->stopRunning();
                    break;
                }

                // This is rare for the example
                if(SPARTA_EXPECT_FALSE(ex_inst.getUnit() == InstArchInfo::TargetUnit::ROB))
                {
                    ILOG("Instigating flush... " << ex_inst);
                    // Signal flush to the system
                    out_retire_flush_.send(ex_inst.getUniqueID());

                    // Redirect fetch
                    out_fetch_flush_redirect_.send(ex_inst.getTargetVAddr() + 4);

                    ++num_flushes_;
                    break;
                }

                // Check to see if this is the last instruction of the
                // trace
                if(ex_inst.getLast()) {
                    rob_stopped_simulation_ = true;
                    rob_drained_notif_source_->postNotification(true);
                    // No need to stop the scheduler -- let simulation
                    // drain normally.  Also, don't need to check forward progress
                }
            }
            else {
                break;
            }
        }

        if(false == reorder_buffer_.empty()) {
            const auto & oldest_inst = reorder_buffer_.front();
            if(oldest_inst->getStatus() == Inst::Status::COMPLETED) {
                ILOG("oldest is marked completed: " << oldest_inst);
                ev_retire_.schedule();
            }
            else if(false == oldest_inst->isMarkedOldest()) {
                ILOG("set oldest: " << oldest_inst);
                oldest_inst->setOldest(true, &ev_retire_);
            }
        }

        if(retired_this_cycle != 0) {
            out_reorder_buffer_credits_.send(retired_this_cycle);
            last_retirement_ = getClock()->currentCycle();
        }
    }

    void ROB::dumpDebugContent_(std::ostream& output) const
    {
        output << "ROB Contents" << std::endl;
        for(const auto & entry : reorder_buffer_) {
            output << '\t' << entry << std::endl;
        }
    }

    // Make sure the pipeline is making forward progress
    void ROB::checkForwardProgress_()
    {
        if(getClock()->currentCycle() - last_retirement_ >= retire_timeout_interval_)
        {
            sparta::SpartaException e;
            e << "Been a while since we've retired an instruction.  Is the pipe stalled indefinitely?";
            e << " currentCycle: "  << getClock()->currentCycle();
            throw e;
        }
        ev_ensure_forward_progress_.schedule(retire_timeout_interval_);
    }

    void ROB::onStartingTeardown_() {
        if ((reorder_buffer_.size() > 0) && (false == rob_stopped_simulation_)) {
            std::cerr << "WARNING! Simulation is ending, but the ROB didn't stop it.  Lock up situation?" << std::endl;
            dumpDebugContent_(std::cerr);
        }
    }

}
