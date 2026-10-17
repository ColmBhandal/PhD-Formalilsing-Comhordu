# src/protocol/: rules for the protocol and its safety proof

- The protocol plugs in through `Protocol.v`, which defines its processes as instances of `ProcNames` and `ProcDefs`, and `ProtocolBridge.v`, which proves that they meet the language's conditions, such as `GuardedDefs`, and holds facts true only of this protocol. Protocol files import `ProtocolBridge`.
