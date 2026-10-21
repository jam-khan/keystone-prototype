"""Small examples of kernel semantics and asynchronous page lifetimes."""

import argparse

from experiments.gather import GatherCase, LeanGather, reference
from experiments.lowering import CudaGather, NativeGather
from experiments.runtime import Controller, PendingGather


def kernel_demo(native, lean):
    case = GatherCase(2, 5, 8, (2, 0, 1), (10, 11, 20, 21, 30, 31))
    model = lean.run(case)
    actual = native.run(case)
    assert model["status"] == "completed"
    assert actual == model["output"] == reference(case)
    print("Gather:", model["output"], "(5 active lanes, 3 padded)")


def lifetime_demo(native):
    controller = Controller(capacity=1)
    a = controller.command("allocate", owner=10)["lease"]
    cache = [101, 102, 103, 104]  # Fill once; keep read-only until completion.
    tickets = [controller.command("submit", owner=10, pages=[a])["ticket"] for _ in range(2)]
    jobs = [PendingGather.from_ticket(ticket, tokens=3) for ticket in tickets]
    controller.command("retire", owner=10)
    allocation = controller.command("allocate", owner=20)
    assert not allocation["accepted"]
    print("Cancel A: B cannot reuse its page while either reader is pending.")
    for job in reversed(jobs):
        case = job.input_now(controller, cache, page_size=4)
        actual = native.run(case)
        completion = controller.command("complete", ticket=job.ticket)
        assert actual == [101, 102, 103] and completion["accepted"]
        if job == jobs[-1]:
            allocation = controller.command("allocate", owner=20)
            assert not allocation["accepted"]

    b = controller.command("allocate", owner=20)["lease"]
    assert b["page"] == a["page"] and b["generation"] > a["generation"]
    cache[:] = [901, 902, 903, 904]
    ticket = controller.command("submit", owner=20, pages=[b])["ticket"]
    before = controller.state
    stale_completion = controller.command("complete", ticket=jobs[0].ticket)
    assert not stale_completion["accepted"]
    assert controller.state == before
    stale_submission = controller.command("submit", owner=20, pages=[a])
    assert not stale_submission["accepted"]
    controller.command("retire", owner=20)
    controller.command("complete", ticket=ticket["id"])
    assert controller.state["allocations"] == []
    print("Both readers finished: B reuses the page; stale A completion is harmless.")

    # Construct the failure that an immediate-free policy would allow.
    late = GatherCase(4, 3, 8, jobs[0].table, tuple(cache))
    actual = native.run(late)
    assert actual == [901, 902, 903]
    print("Premature reuse would make A read", actual, "instead of [101, 102, 103].")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cuda", action="store_true", help="require nvcc and an NVIDIA GPU")
    args = parser.parse_args()
    native = CudaGather() if args.cuda else NativeGather()
    kernel_demo(native, LeanGather())
    lifetime_demo(native)


if __name__ == "__main__":
    main()
