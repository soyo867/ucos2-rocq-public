Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** OSInitHookEnd in the V2.93.01 ARMv7-A port, with CPU hooks enabled
    and interrupt-disable measurement disabled, has an empty selected body.
    Its internal contract consumes and returns the same arbitrary UCOS2
    Assertion P.  The OSInit caller instantiates P at its actual final
    endpoint, including any startup protocol and continuation resources.
    This hook establishes neither an interrupt mask nor new ownership.
    The measurement-enabled variant is outside this selected contract. *)
