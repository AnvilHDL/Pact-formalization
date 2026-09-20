# Atomic Correspondence

[Base.lean](Base.lean) matches atomic decorated steps with compiled edges.

| Theorem | Case |
|---|---|
| `correspondence_skip_stepIff` | Silent idle self-loop in a non-clock environment |
| `correspondence_message_stepIff` | Communication when enabled, silent waiting otherwise; the environment constrains firing |
| `correspondence_tock_stepIff` | Clock completion or non-clock waiting |
| `correspondence_progress_stepIff` | Progress emission followed by completion |
| `correspondence_var_stepIff` | No public step for an open variable; its construction edge is a marker |

[Simultaneous/Base](../Simultaneous/Base.lean) uses these equivalences with the
corresponding base-state guards.
