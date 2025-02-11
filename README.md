# automating-inductiveness

This repository holds specifications for distributed protocols in TLA+ and Ivy. They were used to compare tools to automate finding an inductive invariant that implies safety for these protocols. I have also listed the problems that I faced while using the tools.

## Tools Used

[endive](https://github.com/will62794/endive) ([paper](https://arxiv.org/pdf/2205.06360)): takes TLA+ Specification (protocol.tla) and configuration file (protocol.config.json)

[SWISS](https://github.com/secure-foundations/SWISS) ([paper](https://www.andrew.cmu.edu/user/bparno/papers/swiss.pdf)): takes Ivy Specification (protocol.ivy) and configuration file (protocol.config)

## Protocols

[Ben-Or Byzantine Consensus Protocol](https://dl.acm.org/doi/pdf/10.1145/800221.806707)

Some simplifications to Ben-Or were made to reduce its state space.

[Bracha Byzantine Consensus Protocol](https://core.ac.uk/download/pdf/82523202.pdf)
