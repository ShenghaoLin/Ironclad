include "../../Common/Framework/Main.s.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Framework/Environment.s.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Impl/Lock/PacketParsing.i.dfy"
include "../../Impl/Lock/UdpLock.i.dfy"
include "../../Impl/Lock/Host.i.dfy"
include "AbstractService.s.dfy"
include "../../Protocol/Lock/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Lock/RefinementProof/RefinementProof.i.dfy"
include "Marshall.i.dfy"

// mono tools/Dafny/Dafny.exe /allowGlobals /noNLarith /autoTriggers:1 /z3opt:nlsat.randomize=false /warnShadowing /ironDafny src/Dafny/Distributed/Services/Lock/ShenghaoMain.i.dfy 

module Main_i refines Main_s{
    import opened DistributedSystem_i
    import opened Environment_s
    import opened Concrete_NodeIdentity_i
    import opened PacketParsing_i
    import opened UdpLock_i
    import opened Host_i
    import opened AbstractServiceLock_s
    import opened Refinement_i
    import opened MarshallProof_i

    //=====================================DS_State=====================================

    lemma OnlyMarshallableData(db:seq<DS_State>, config:Config)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures forall i :: 0 <= i < |db| 
                    ==> 
                        forall p :: p in db[i].environment.sentPackets && p.src in db[i].servers
                            ==> Demarshallable(p.msg, CMessageGrammar());
    {
        if (|db| == 1) {
            assert(|db[0].environment.sentPackets| == 0);
        }
        else {
            OnlyMarshallableData(db[0..|db| - 1], config);
            var i := |db| - 2;
            assert(DS_Next(db[i], db[i + 1]));
            
            if db[i].environment.nextStep.LEnvStepHostIos? && db[i].environment.nextStep.actor in db[i].servers {
                assert(DS_NextOneServer(db[i], db[i + 1], db[i].environment.nextStep.actor, db[i].environment.nextStep.ios));
                assert(OnlySentMarshallableData(db[i].environment.nextStep.ios));
                var ios := db[i].environment.nextStep.ios;
                var e := db[i].environment;
                var e' := db[i + 1].environment;
                if (e.nextStep.LEnvStepHostIos?) {
                    assert(forall p :: p in e.sentPackets && p.src in db[i].servers ==> Demarshallable(p.msg, CMessageGrammar()));
                    assert(e'.sentPackets == e.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s));
                    assert(forall p :: p in ios && p.LIoOpSend? ==>  Demarshallable(p.s.msg, CMessageGrammar()));
                    assert(forall p :: p in e'.sentPackets && p.src in db[i].servers ==> Demarshallable(p.msg, CMessageGrammar()));
                }
                else {
                    assert(e'.sentPackets == e.sentPackets);
                }
            }
            else {
                assert(forall p :: p in db[i + 1].environment.sentPackets && p.src in db[i + 1].servers ==> p in db[i].environment.sentPackets);
            }
        }
    }

    //=====================================LS_State=====================================

    function AbstractifyConcretePacket(p:LPacket<EndPoint,seq<byte>>) : LPacket<EndPoint, LockMessage>
        ensures p.dst == AbstractifyConcretePacket(p).dst;
        ensures p.src == AbstractifyConcretePacket(p).src;
        ensures AbstractifyCMessage(DemarshallData(p.msg)) == AbstractifyConcretePacket(p).msg;
    {
        LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)))
    }

    function SBToLM(msg: seq<byte>) : LockMessage
    {
        AbstractifyCMessage(DemarshallData(msg))
    }

    function LockSentPackets(m: set<LPacket<EndPoint, seq<byte>>>): set<LPacket<EndPoint, LockMessage>>
        ensures forall msg :: msg in m ==> AbstractifyConcretePacket(msg) in LockSentPackets(m);
    {
        set k | k in m:: AbstractifyConcretePacket(k)
    }

    function LockSeqMsg(s: seq<LPacket<EndPoint, seq<byte>>>) : seq<LPacket<EndPoint, LockMessage>>
    {
        if |s| == 0 then [] else LockSeqMsg(s[0..|s|-1]) + [AbstractifyConcretePacket(s[|s| - 1])]
    }

    function LockLHostInfo(m: LHostInfo<EndPoint, seq<byte>>): LHostInfo<EndPoint, LockMessage>
    {
        LHostInfo(LockSeqMsg(m.queue))
    }

    function LockLHost(m: map<EndPoint, LHostInfo<EndPoint, seq<byte>>>): map<EndPoint, LHostInfo<EndPoint, LockMessage>>
    {
        map k | k in m :: LockLHostInfo(m[k])
    }

    function HostStateMapToNodeMap_Init(m: map<EndPoint, HostState>, config: ConcreteConfiguration): map<EndPoint, Node>
        reads *;
        requires MapSeqToSet(config, x=>x) == mapdomain(m);
        requires forall k :: k in m ==> HostInit(m[k], config, k);
        requires SeqIsUnique(config);
        ensures mapdomain(m) == mapdomain(HostStateMapToNodeMap(m, config));
        ensures forall k :: k in HostStateMapToNodeMap(m, config) ==> config == HostStateMapToNodeMap(m, config)[k].config;
        ensures forall k :: k in HostStateMapToNodeMap(m, config) ==> k in m;
        ensures forall k :: 0 <= k < |config| ==> config[k] in HostStateMapToNodeMap(m, config);
        ensures forall k :: k in HostStateMapToNodeMap(m, config) ==> config[int(m[k].node_impl.node.my_index)] == k;
        ensures forall k :: k in HostStateMapToNodeMap(m, config) ==> NodeInit(HostStateMapToNodeMap(m, config)[k],
                                                                               int(m[k].node_impl.node.my_index),
                                                                               config);
        ensures forall k :: 0 <= k < |config| ==> NodeInit(HostStateMapToNodeMap(m, config)[config[k]],
                                                           int(m[config[k]].node_impl.node.my_index),
                                                           config);
        ensures forall k :: 0 <= k < |config| ==> NodeInit(HostStateMapToNodeMap(m, config)[config[k]],
                                                           k,
                                                           config);
    {
        assert(forall k :: k in config ==> k in m);
        assert(forall k:: 0 <= k < |config| ==> config[k] in m);
        assert(forall k :: k in m ==> HostInit(m[k], config, k));
        assert(forall k :: k in m ==> config[int(m[k].node_impl.node.my_index)] == k);
        assert(forall k :: 0 <= k < |config| ==> config[int(m[config[k]].node_impl.node.my_index)] == config[k]);
        assert(SeqIsUnique(config));
        reveal_SeqIsUnique();
        assert(forall k:: 0 <= k < |config| && 0 <= int(m[config[k]].node_impl.node.my_index) < |config| && config[int(m[config[k]].node_impl.node.my_index)] == config[k] 
                        ==> int(m[config[k]].node_impl.node.my_index) == k);
        assert(forall k :: 0 <= k < |config| ==> int(m[config[k]].node_impl.node.my_index) == k);
        map k | k in m :: m[k].node
    }

    function HostStateMapToNodeMap(m: map<EndPoint, HostState>, config: ConcreteConfiguration): map<EndPoint, Node>
    {
        map k | k in m :: m[k].node
    }

    function LockLIoOP(io: LIoOp<EndPoint, seq<byte>>): LIoOp<EndPoint, LockMessage>
        ensures io.LIoOpReceive? == LockLIoOP(io).LIoOpReceive?;
        ensures io.LIoOpSend? == LockLIoOP(io).LIoOpSend?;
    {
        match io {
            case LIoOpSend(s) => LIoOpSend(AbstractifyConcretePacket(s))
            case LIoOpReceive(s) => LIoOpReceive(AbstractifyConcretePacket(s))
            case LIoOpTimeoutReceive => LIoOpTimeoutReceive()
            case LIoOpReadClock(t) => LIoOpReadClock(t)
        }
    }

    function LockSeqLIoOP(ios: seq<LIoOp<EndPoint, seq<byte>>>): seq<LIoOp<EndPoint, LockMessage>>
        ensures |ios| == |LockSeqLIoOP(ios)|;
        ensures forall i :: 0 <= i < |ios| ==> LockLIoOP(ios[i]) == LockSeqLIoOP(ios)[i];
        ensures forall i :: 0 <= i < |ios| ==> ios[i].LIoOpReceive? == LockSeqLIoOP(ios)[i].LIoOpReceive?;
        ensures forall i :: 0 <= i < |ios| ==> ios[i].LIoOpSend? == LockSeqLIoOP(ios)[i].LIoOpSend?;
    {
        assert(|ios| > 0 ==> LockLIoOP(ios[|ios|-1]).LIoOpReceive? == ios[|ios|-1].LIoOpReceive?);
        assert(|ios| > 0 ==> LockLIoOP(ios[|ios|-1]).LIoOpSend? == ios[|ios|-1].LIoOpSend?);
        if |ios| == 0 then [] else LockSeqLIoOP(ios[0..|ios|-1]) + [LockLIoOP(ios[|ios|-1])]
    }

    function LockLEnvNextStep(ns: LEnvStep<EndPoint, seq<byte>>): LEnvStep<EndPoint, LockMessage>
    {
        match ns {
            case LEnvStepHostIos(actor, ios) => LEnvStepHostIos(actor, LockSeqLIoOP(ios))
            case LEnvStepDeliverPacket(p) => LEnvStepDeliverPacket(AbstractifyConcretePacket(p))
            case LEnvStepAdvanceTime => LEnvStepAdvanceTime()
            case LEnvStepStutter => LEnvStepStutter()
        }
    }

    function LEnvToLockEnv(le: LEnvironment<EndPoint, seq<byte>>) : LEnvironment<EndPoint, LockMessage>
    {
        LEnvironment(le.time, LockSentPackets(le.sentPackets), LockLHost(le.hostInfo), LockLEnvNextStep(le.nextStep))
    }

    lemma ValidLIoOP(io:LIoOp<EndPoint, seq<byte>>, actor:EndPoint, e:LEnvironment<EndPoint, seq<byte>>)
        requires IsValidLIoOp(io, actor, e);
        ensures IsValidLIoOp(LockLIoOP(io), actor, LEnvToLockEnv(e));
    {
        match io {
            case LIoOpSend(s) => {
                assert(s.src == actor);
                assert(LockLIoOP(io).s.src == s.src);
                assert(LockLIoOP(io).s.src == actor);
            }
            case LIoOpReceive(r) => {
                assert(r.dst == actor);
                assert(LockLIoOP(io).r.dst == r.dst);
                assert(LockLIoOP(io).r.dst == actor);
            }
            case LIoOpTimeoutReceive => {
                assert(LockLIoOP(io) == LIoOpTimeoutReceive());
            }
            case LIoOpReadClock(t) => {
                assert(LockLIoOP(io) == LIoOpReadClock(t));
            }
        }
    }

    lemma ValidSeqLIoOP(ios:seq<LIoOp<EndPoint, seq<byte>>>, actor:EndPoint, e:LEnvironment<EndPoint, seq<byte>>)
        requires forall io :: io in ios ==> IsValidLIoOp(io, actor, e);
        ensures forall io :: io in ios ==> IsValidLIoOp(LockLIoOP(io), actor, LEnvToLockEnv(e));
    {
        var i := 0;
        while i < |ios|
        {
            ValidLIoOP(ios[i], actor, e);
            i := i + 1;
        }
    }

    lemma CompatibleLIoOpSeq(ios:seq<LIoOp<EndPoint, seq<byte>>>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        ensures LIoOpSeqCompatibleWithReduction(LockSeqLIoOP(ios));
    {
        assert(|ios| == |LockSeqLIoOP(ios)|);
        assert(forall i :: 0 <= i < |ios| ==> ios[i].LIoOpReceive? == LockSeqLIoOP(ios)[i].LIoOpReceive?);
    }

    lemma LEnvironmentToLockEnvValidNextStep(le: LEnvironment<EndPoint, seq<byte>>)
        requires IsValidLEnvStep(le, le.nextStep)
        ensures IsValidLEnvStep(LEnvToLockEnv(le), LEnvToLockEnv(le).nextStep)
    {
        match le.nextStep {
            case LEnvStepHostIos(actor, ios) => {
                assert(LEnvToLockEnv(le).nextStep == LEnvStepHostIos(actor, LockSeqLIoOP(ios)));
                assert(LockSeqLIoOP(ios) == LEnvToLockEnv(le).nextStep.ios);
                assert(LEnvToLockEnv(le).nextStep.actor == actor);
                assert(forall io :: io in ios ==> IsValidLIoOp(io, actor, le));
                ValidSeqLIoOP(ios, actor, le);
                assert(forall i :: 0 <= i < |LockSeqLIoOP(ios)| ==> LockSeqLIoOP(ios)[i] == LockLIoOP(ios[i]));
                assert(forall io :: io in LEnvToLockEnv(le).nextStep.ios ==> IsValidLIoOp(io, actor, LEnvToLockEnv(le)));
                CompatibleLIoOpSeq(ios);
            }
            case LEnvStepDeliverPacket(p) => {
                assert(LEnvToLockEnv(le).nextStep == LEnvStepDeliverPacket(AbstractifyConcretePacket(p)));
                assert(LEnvToLockEnv(le).sentPackets == LockSentPackets(le.sentPackets));
                assert(forall m :: m in le.sentPackets ==> AbstractifyConcretePacket(m) in LEnvToLockEnv(le).sentPackets);
                assert(exists m :: m in le.sentPackets ==> LEnvToLockEnv(le).nextStep.p == AbstractifyConcretePacket(m));
                assert(LEnvToLockEnv(le).nextStep.p in LEnvToLockEnv(le).sentPackets);
                assert(IsValidLEnvStep(LEnvToLockEnv(le), LEnvToLockEnv(le).nextStep));
            }
            case LEnvStepAdvanceTime => {
                assert(LEnvToLockEnv(le).nextStep == LEnvStepAdvanceTime());
                assert(IsValidLEnvStep(LEnvToLockEnv(le), LEnvToLockEnv(le).nextStep));
            }
            case LEnvStepStutter => {
                assert(LEnvToLockEnv(le).nextStep == LEnvStepStutter());
                assert(IsValidLEnvStep(LEnvToLockEnv(le), LEnvToLockEnv(le).nextStep));
            }
        }
    }

    function DSStateToLSState_Init(ds:DS_State, config:ConcreteConfiguration): LS_State
        reads *;
        requires DS_Init(ds, config);
        ensures mapdomain(ds.servers) == mapdomain(DSStateToLSState(ds, config).servers);
        ensures DSStateToLSState_Init(ds, config) == DSStateToLSState(ds, config);
    {
        assert(ConcreteConfigInit(config, mapdomain(ds.servers), ds.clients));
        assert(SeqIsUnique(config));
        assert(forall k :: k in ds.servers ==> HostInit(ds.servers[k], config, k));
        LS_State(LEnvToLockEnv(ds.environment), HostStateMapToNodeMap_Init(ds.servers, config))
    }

    function DSStateToLSState(ds:DS_State, config:ConcreteConfiguration): LS_State
        reads *;
        ensures mapdomain(ds.servers) == mapdomain(DSStateToLSState(ds, config).servers); 
    {
        LS_State(LEnvToLockEnv(ds.environment), HostStateMapToNodeMap(ds.servers, config))
    }

    lemma DStoLS(config:ConcreteConfiguration, db:seq<DS_State>) returns (lb:seq<LS_State>)
        requires |db| > 0;
        requires DS_Init(db[0], config);
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures |db| == |lb|;
        ensures LS_Init(lb[0], config);
        ensures forall i :: 0 <= i < |lb| ==> forall m :: m in lb[i].servers <==> m in db[i].servers;
        ensures lb[|lb| - 1] == DSStateToLSState(db[|db| - 1], config);
        ensures forall i :: 0 <= i < |db| ==> forall m :: m in db[i].environment.sentPackets ==> AbstractifyConcretePacket(m) in lb[i].environment.sentPackets;
        ensures forall i{:trigger LS_Next(lb[i], lb[i + 1])} :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i + 1]);
    {
        if (|db| == 1) {
            assert(ValidConfig(config));
            assert(SeqIsUnique(config));
            assert(|config| > 0);
            assert(ConcreteConfigInit(config, mapdomain(db[0].servers), db[0].clients));
            assert(forall e :: e in config <==> e in db[0].servers);
            assert(LEnvironment_Init(db[0].environment));
            lb := [DSStateToLSState_Init(db[0], config)];
        }
        else {
            var prev := DStoLS(config, db[0..|db| - 1]);
            var k := |db| - 2;
            var s := DSStateToLSState(db[k], config);
            var s' := DSStateToLSState(db[k + 1], config);
            assert(prev[|prev| - 1] == s);
            lb := prev + [s'];
            assert(0 <= k < |db| - 1);
            assert(DS_Next(db[k], db[k + 1]));
            assert(IsValidLEnvStep(db[|db| - 2].environment, db[|db| - 2].environment.nextStep));
            assert(s.environment == LEnvToLockEnv(db[|db| - 2].environment));
            LEnvironmentToLockEnvValidNextStep(db[|db| - 2].environment);
            assert(LEnvironment_Next(s.environment,
                                     s'.environment));
            if (s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers) {
                assert(NodeNext(s.servers[s.environment.nextStep.actor], s'.servers[s.environment.nextStep.actor], s.environment.nextStep.ios));
            }
            else {
                assert(s'.servers == s.servers);
            }
            assert(LS_Next(s, s'));
        }
    }

    //=====================================GLS_State=====================================

    function LSStateToGLSState(ls:LS_State, gls_prev:GLS_State, config:ConcreteConfiguration) : GLS_State
        requires LS_Next(gls_prev.ls, ls);
        ensures GLS_Next(gls_prev, LSStateToGLSState(ls, gls_prev, config));
    {
        if gls_prev.ls.environment.nextStep.LEnvStepHostIos? && gls_prev.ls.environment.nextStep.actor in gls_prev.ls.servers
            && NodeGrant(gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor], ls.servers[gls_prev.ls.environment.nextStep.actor], gls_prev.ls.environment.nextStep.ios)
            && gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor].held && gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF then
            GLS_State(ls, gls_prev.history + [gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor].config[(gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor].my_index + 1) % |gls_prev.ls.servers[gls_prev.ls.environment.nextStep.actor].config|]])
        else GLS_State(ls, gls_prev.history)
    }

    lemma LSToGLS(lb:seq<LS_State>, config:ConcreteConfiguration) returns (glb:seq<GLS_State>) 
        requires |lb| > 0;
        requires LS_Init(lb[0], config);
        requires forall i{:trigger LS_Next(lb[i], lb[i + 1])} :: 0 <= i < |lb| - 1 ==> LS_Next(lb[i], lb[i + 1]);
        ensures |lb| == |glb|;
        ensures GLS_Init(glb[0], config);
        ensures forall i :: 0 <= i < |glb| ==> glb[i].ls == lb[i];
        ensures forall i{:trigger GLS_Next(glb[i], glb[i + 1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i + 1])
    {
        if (|lb| == 1) {
            var gls := GLS_State(lb[0], [config[0]]);
            assert(GLS_Init(gls, config));
            glb := [gls];
        }
        else {
            var prev := LSToGLS(lb[0..|lb| - 1], config);
            var gls_prev := prev[|prev| - 1];
            var k := |lb| - 2;
            assert(gls_prev.ls == lb[k]);
            assert(LS_Next(lb[k], lb[k + 1]));
            var gls_new := LSStateToGLSState(lb[k + 1], gls_prev, config);
            assert(GLS_Next(gls_prev, gls_new));
            var s := gls_prev.ls;
            var s' := gls_new.ls;
            assert(LS_Next(s, s'));
            LS_ServerInvariant(s, s');
            glb := prev + [gls_new];
        }
    }

    //=========================================Invariant Proof===========================

    lemma LS_ServerInvariant(s:LS_State, s':LS_State)
        requires LS_Next(s, s');
        ensures Collections__Maps2_s.mapdomain(s.servers) == Collections__Maps2_s.mapdomain(s'.servers);
    {
        if (s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers) {
            var id := s.environment.nextStep.actor;
            assert(LS_NextOneServer(s, s', id, s.environment.nextStep.ios));
            assert(s'.servers == s.servers[id := s'.servers[id]]);
            assert(id in s.servers);
            assert(Collections__Maps2_s.mapdomain(s.servers) == Collections__Maps2_s.mapdomain(s'.servers));
        }
        else {
            assert(s.servers == s'.servers);
        }
    }

    lemma GLS_Seq_ServerInvariant(glb:seq<GLS_State>, config:Config) 
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i{:trigger GLS_Next(glb[i], glb[i + 1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i + 1]);
        ensures forall i :: 0 <= i < |glb| ==> forall e :: e in config <==> e in glb[i].ls.servers;
    {
        if (|glb| == 1) {
            var s := glb[0].ls;
            assert(GLS_Init(glb[0], config));
            assert(LS_Init(glb[0].ls, config));
            assert(forall e :: e in config <==> e in s.servers);
        }
        else {
            GLS_Seq_ServerInvariant(glb[0..|glb| - 1], config);
            var i := |glb| - 2;
            assert(GLS_Next(glb[i], glb[i + 1]));
            assert(LS_Next(glb[i].ls, glb[i + 1].ls));
            var s := glb[i].ls;
            var s' := glb[i + 1].ls;
            LS_ServerInvariant(s, s');
            assert(forall e :: e in config <==> e in s.servers);
            assert(Collections__Maps2_s.mapdomain(s.servers) == Collections__Maps2_s.mapdomain(s'.servers));
            assert(forall e :: e in config <==> e in s'.servers);
        }
    }


    lemma NodeNext_ConfigInvariant(s:Node, s':Node, ios:seq<LockIo>)
        requires NodeNext(s, s', ios);
        ensures s.config == s'.config;
    {
        
        if NodeGrant(s, s', ios) {
            if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF {
                assert(s'.config == s.config);
            } 
            else{
                assert(s == s');
            }
        }
        else {
            assert(NodeAccept(s, s', ios)); 
            if ios[0].LIoOpTimeoutReceive? {
                assert(s == s');
            }
            else  {
                assert(ios[0].LIoOpReceive?);
                if (!s.held 
                    && ios[0].r.src in s.config
                    && ios[0].r.msg.Transfer? 
                    && ios[0].r.msg.transfer_epoch > s.epoch) {
                        assert(s'.config == s.config);
                }
                else {
                    assert(s == s');
                }
            }
        }
    }

    lemma LS_Next_ConfigInvariant(s:LS_State, s':LS_State)
        requires LS_Next(s, s');
        ensures mapdomain(s'.servers) == mapdomain(s.servers);
        ensures forall m :: m in s'.servers ==> s.servers[m].config == s'.servers[m].config;
    {
        LS_ServerInvariant(s, s');
        assert(mapdomain(s'.servers) == mapdomain(s.servers));
        if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers {
            assert(LS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios));
            var id := s.environment.nextStep.actor;
            var ios := s.environment.nextStep.ios;
            assert(s'.servers == s.servers[id := s'.servers[id]]);
            assert(NodeNext(s.servers[id], s'.servers[id], ios));
            NodeNext_ConfigInvariant(s.servers[id], s'.servers[id], ios);
            assert(s.servers[id].config == s'.servers[id].config);
        }
        else {
            assert(s'.servers == s.servers);
        }
    }

    lemma GLS_ConfigInvariant(glb:seq<GLS_State>, config:Config)
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i{:trigger GLS_Next(glb[i], glb[i + 1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i + 1]);
        ensures forall i :: 0 <= i < |glb| ==> forall s :: s in glb[i].ls.servers ==> glb[i].ls.servers[s].config == config;
    {
        if (|glb| == 1) {
            var s := glb[0].ls;
            assert(GLS_Init(glb[0], config));
            assert(LS_Init(glb[0].ls, config));
            assert(forall e :: e in config <==> e in s.servers);
            assert(forall index :: 0 <= index < |config| ==> NodeInit(s.servers[config[index]], index, config));
            assert(forall index :: 0 <= index < |config| ==> s.servers[config[index]].config == config);
            assert(forall e :: e in s.servers ==> s.servers[e].config == config);
        }
        else {
            GLS_ConfigInvariant(glb[0..|glb| - 1], config);
            var i := |glb| - 2;
            assert(GLS_Next(glb[i], glb[i + 1]));
            assert(LS_Next(glb[i].ls, glb[i + 1].ls));
            var s := glb[i].ls;
            var s' := glb[i + 1].ls;
            LS_Next_ConfigInvariant(s, s');
            assert(forall m :: m in s.servers ==> s.servers[m].config == config);
            assert(forall m :: m in s'.servers ==> s.servers[m].config == s'.servers[m].config);
            assert(forall m :: m in s'.servers ==> s'.servers[m].config == config);
        }
    }

    predicate LockInvariant(s:GLS_State, config:Config)
    {
        |s.history| >= 1 &&
        (forall m :: m in s.history ==> m in s.ls.servers) &&
        (forall ser :: ser in s.ls.servers && s.ls.servers[ser].held 
                ==> 
                    s.ls.servers[ser].epoch == |s.history|
                    && ser == s.history[|s.history| - 1]) &&
        (forall i :: 0 <= i < |s.history| - 1 
                ==> 
                    s.history[i] in s.ls.servers && s.ls.servers[s.history[i]].epoch >= i + 1) &&
        (forall mt :: mt in s.ls.environment.sentPackets 
                    && mt.src in s.ls.servers 
                    && mt.msg.Transfer? 
                ==> 
                    0 <= mt.msg.transfer_epoch - 1 < |s.history|
                    && s.history[mt.msg.transfer_epoch - 1] == mt.dst) &&
        (forall ml :: ml in s.ls.environment.sentPackets
                    && ml.src in s.ls.servers
                    && ml.msg.Locked?
                ==>
                    1 <= ml.msg.locked_epoch <= |s.history|
                    && s.history[ml.msg.locked_epoch - 1] == ml.src) &&
        (forall mm :: mm in s.ls.servers <==> mm in config) &&
        (forall ms :: ms in s.ls.servers ==> s.ls.servers[ms].config == config)
    }

    lemma LockTransition(s: GLS_State, s':GLS_State, config:Config)
        requires GLS_Next(s, s');
        requires LockInvariant(s, config);

        ensures LockInvariant(s', config);
        
    {
        var ls := s.ls;
        var ls' := s'.ls;
        assert(forall m :: m in ls.servers <==> m in ls'.servers);
        assert(forall m :: m in s.ls.servers <==> m in config);
        assert(forall m :: m in ls.servers ==> ls.servers[m].config == ls.servers[m].config);
        assert(forall m :: m in ls'.servers <==> m in config);
        if ls.environment.nextStep.LEnvStepHostIos? && ls.environment.nextStep.actor in ls.servers {
            assert(LS_NextOneServer(ls, ls', ls.environment.nextStep.actor, ls.environment.nextStep.ios));
            var ios := ls.environment.nextStep.ios;
            var actor := ls.environment.nextStep.actor;
            var node := ls.servers[actor];
            var node' := ls'.servers[actor];
            assert(ls'.servers == ls.servers[actor := ls'.servers[actor]]);
            assert(actor in ls.servers);
            assert(actor in ls'.servers);
            if (NodeGrant(node, node', ios)) {
                if node.held && node.epoch < 0xFFFF_FFFF_FFFF_FFFF {
                    assert(s'.history == s.history + [node.config[(node.my_index + 1) % |node.config|]]);
                    assert(node.config[(node.my_index + 1) % |node.config|] == ios[0].s.dst);
                    assert(node.config[(node.my_index + 1) % |node.config|] in s'.ls.servers);
                    assert(ios[0].s.msg.transfer_epoch == node.epoch + 1);
                    assert(ios[0].s.msg.transfer_epoch == |s'.history|);
                    assert(ls'.environment.sentPackets == ls.environment.sentPackets + {ios[0].s});
                    assert(forall m :: m in s'.ls.environment.sentPackets 
                                    && m.src in s'.ls.servers 
                                    && m.msg.Transfer? 
                                ==> 
                                    0 <= m.msg.transfer_epoch - 1 < |s'.history|
                                    && s'.history[m.msg.transfer_epoch - 1] == m.dst);
                    assert(0 <= ios[0].s.msg.transfer_epoch - 1 < |s'.history|);
                    assert(|s.history| >= 1);
                    assert(|s'.history| >= 2);
                    assert(node'.epoch == node.epoch == |s.history| == |s'.history| - 1);
                    var i := |s'.history| - 2;
                    assert(i == |s.history| - 1);
                    assert(s'.history[i] == s.history[i] == actor);
                    assert(s'.ls.servers[s'.history[i]].epoch == s.ls.servers[s.history[i]].epoch == i + 1);
                    assert(forall ii :: 0 <= ii < |s'.history| - 1 
                                ==> 
                                  s'.history[ii] in s'.ls.servers && s'.ls.servers[s'.history[ii]].epoch >= ii + 1);
                    assert(forall m :: m in ls.servers && ls.servers[m].held ==> m == s.history[i]);
                    assert(forall m :: m in ls.servers && ls.servers[m].held ==> !ls'.servers[m].held);
                    assert(forall m :: m in ls'.servers && ls'.servers[m].held ==> ls'.servers[m].epoch == |s'.history|);
                    assert(
                        forall m :: m in s'.ls.environment.sentPackets
                                    && m.msg.Locked?
                                ==>
                                    m in s.ls.environment.sentPackets
                    );
                }
                else  {
                    assert(ls'.servers == ls.servers);
                    assert(s'.history == s.history);
                    assert(
                        forall m :: m in ls'.environment.sentPackets 
                                    && m.src in ls'.servers 
                                    && m.msg.Transfer? 
                        ==> m in ls.environment.sentPackets
                    );
                    assert(
                        forall m :: m in s'.ls.environment.sentPackets
                                && m.msg.Locked?
                            ==>
                                m in s.ls.environment.sentPackets
                    );
                }
            }
            else {
                assert(NodeAccept(node, node', ios));
                if (ios[0].LIoOpTimeoutReceive?) {
                    assert(ls'.servers == ls.servers);
                    assert(s'.history == s.history);
                    assert(
                        forall m :: m in ls'.environment.sentPackets 
                                    && m.src in ls'.servers 
                                    && m.msg.Transfer? 
                        ==> m in ls.environment.sentPackets
                    );
                    assert(
                        forall m :: m in s'.ls.environment.sentPackets
                                    && m.msg.Locked?
                                ==>
                                    m in s.ls.environment.sentPackets
                    );
                }
                else if (!node.held 
                         && ios[0].r.src in node.config
                         && ios[0].r.msg.Transfer? 
                         && ios[0].r.msg.transfer_epoch > node.epoch) {
                    assert(s.history == s'.history);
                    assert(ios[0].r in ls.environment.sentPackets && ios[0].r.src in ls.servers);
                    assert(ios[0].r.dst in s.history);
                    assert(IsValidLEnvStep(ls.environment, ls.environment.nextStep));
                    assert(forall io :: io in ios ==> IsValidLIoOp(io, actor, ls.environment));
                    assert(forall io :: io in ios && io.LIoOpReceive? ==> io.r.dst == actor);
                    assert(ios[0].r.dst == actor);
                    assert(exists i :: 0 <= i < |s.history| ==> s.history[i] == ios[0].r.dst);
                    assert(forall i :: 0 <= i < |s.history| - 1 && s.history[i] == actor ==> node.epoch >= i + 1);
                    assert(s.history[|s.history| - 1] == ios[0].r.dst);
                    assert(node'.epoch > node.epoch);
                    var m := ios[0].r;
                    assert(forall i :: 0 <= i < |s.history| - 1 && s.history[i] == m.dst ==> m.msg.transfer_epoch > i + 1);
                    assert(m.msg.transfer_epoch == |s.history|);
                    assert(node'.held);
                    assert(node'.epoch == m.msg.transfer_epoch == |s'.history|);
                    assert(s'.history[|s'.history| - 1] == actor);
                    assert(
                        forall i :: 0 <= i < |s'.history| - 1 
                            ==> 
                                s'.history[i] in s'.ls.servers && s'.ls.servers[s'.history[i]].epoch >= i + 1
                    );
                    assert(ios[1].s.msg.locked_epoch == |s'.history|);
                    assert(
                        forall md :: md in s'.ls.environment.sentPackets
                                    && md.msg.Locked?
                                ==>
                                    md in s.ls.environment.sentPackets
                                    || md == ios[1].s
                    );
                }
                else {
                    assert(ls'.servers == ls.servers);
                    assert(s'.history == s.history);
                    assert(
                        forall m :: m in ls'.environment.sentPackets 
                                    && m.src in ls'.servers 
                                    && m.msg.Transfer? 
                        ==> m in ls.environment.sentPackets
                    );
                    assert(
                        forall m :: m in s'.ls.environment.sentPackets
                                    && m.msg.Locked?
                                ==>
                                    m in s.ls.environment.sentPackets
                    );
                }
            }
        }
        else {
            assert(ls'.servers == ls.servers);
            assert(s'.history == s.history);
            assert(
                forall m :: m in ls'.environment.sentPackets 
                            && m.src in ls'.servers 
                            && m.msg.Transfer? 
                ==> m in ls.environment.sentPackets
            );
            assert(
                forall m :: m in s'.ls.environment.sentPackets
                            && m.msg.Locked?
                            && m.src in ls'.servers
                        ==>
                            m in s.ls.environment.sentPackets
            );
        }
    }


    lemma LockIsUnique(glb:seq<GLS_State>, config:Config) 
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i{:trigger GLS_Next(glb[i], glb[i + 1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i + 1]);
        ensures forall i :: 0 <= i < |glb| ==> LockInvariant(glb[i], config);
    {
        if (|glb| == 1) {
            assert(GLS_Init(glb[0], config));
            var servers := glb[0].ls.servers;
            assert(forall index :: 0 <= index < |config| ==> NodeInit(servers[config[index]], index, config));
            assert(forall m :: m in servers <==> m in config);
            assert(forall m :: m in servers ==> servers[m].config == config);
            assert(|glb[0].history| == 1);
            assert(glb[0].history[0] in config);
            assert(glb[0].history[0] in servers);
            assert(forall m :: m in glb[0].history ==> m in servers);
            assert(forall e :: e in config <==> e in servers);
            assert(forall i :: 0 <= i < |config| ==> servers[config[i]].held == (i == 0));
            assert(forall m :: m in servers && servers[m].held ==> m == config[0]);
            assert(LockInvariant(glb[0], config));
        } 
        else {
            LockIsUnique(glb[0..|glb| - 1], config);
            var i := |glb| - 2;
            assert(i >= 0);
            assert(GLS_Next(glb[i], glb[i + 1]));
            LockTransition(glb[i], glb[i + 1], config);
            assert(LockInvariant(glb[|glb| - 1], config));
        }
    }

    // =================================GLS Correspondence=========================================

    predicate GLS_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, gls:GLS_State) 
    {
        forall p, epoch :: 
            p in concretePkts 
        && p.src in gls.ls.servers 
        && p.dst in gls.ls.servers 
        && p.msg == MarshallLockMsg(epoch) 
        ==>
            1 <= epoch <= |gls.history|
        && p.src == gls.history[epoch-1]               
    } 

    lemma GLS_Correspondence_Proof(gls:GLS_State, config:Config, concretePkts:set<LPacket<EndPoint, seq<byte>>>)
        requires LockInvariant(gls, config);
        requires forall p :: p in concretePkts && p.src in gls.ls.servers 
                        ==> 
                            Demarshallable(p.msg, CMessageGrammar())
                            && AbstractifyConcretePacket(p) in gls.ls.environment.sentPackets;
        ensures GLS_Correspondence(concretePkts, gls);
    {
        forall p, epoch |
                p in concretePkts 
                && p.src in gls.ls.servers 
                && p.dst in gls.ls.servers 
                && p.msg == MarshallLockMsg(epoch) 
            ensures 1 <= epoch <= |gls.history|;
            ensures p.src == gls.history[epoch - 1];
        {
            var np := AbstractifyConcretePacket(p);
            assert(Demarshallable(p.msg, CMessageGrammar()));
            lemma_ParseMarshallLockedAbstract(p.msg, epoch, np.msg);
            assert(np.msg.Locked?);
            assert(np.msg.locked_epoch == epoch);
            assert(np in gls.ls.environment.sentPackets);
            assert(1 <= np.msg.locked_epoch <= |gls.history|);
            assert(np.src == p.src);
            assert(gls.history[np.msg.locked_epoch - 1] == np.src);
        }
    }

    lemma GLS_Cor_Seq(db:seq<DS_State>, glb:seq<GLS_State>, config:Config)
        requires |db| == |glb|;
        requires forall i :: 0 <= i < |glb| ==> LockInvariant(glb[i], config);
        requires forall i :: 0 <= i < |glb| ==> forall m :: m in glb[i].ls.servers <==> m in db[i].servers;
        requires forall i :: 0 <= i < |db| 
                        ==> 
                            forall p :: p in db[i].environment.sentPackets && p.src in db[i].servers
                                    ==> 
                                        Demarshallable(p.msg, CMessageGrammar()) 
                                        && AbstractifyConcretePacket(p) in glb[i].ls.environment.sentPackets;
        ensures forall i :: 0 <= i < |glb| ==> GLS_Correspondence(db[i].environment.sentPackets, glb[i])
    {
        assert(
            forall i :: 0 <= i < |db| 
                ==> 
                    forall p :: p in db[i].environment.sentPackets && p.src in glb[i].ls.servers
                            ==> 
                                Demarshallable(p.msg, CMessageGrammar()) 
                                && AbstractifyConcretePacket(p) in glb[i].ls.environment.sentPackets
        );
        forall i | 0 <= i < |glb|
            ensures GLS_Correspondence(db[i].environment.sentPackets, glb[i])
        {
            GLS_Correspondence_Proof(glb[i], config, db[i].environment.sentPackets);
        }
    }

    //==========================================Service State=============================

    lemma GLSToSS(glb:seq<GLS_State>, config:ConcreteConfiguration) returns (sb:seq<ServiceState>)
        requires |glb| > 0;
        requires GLS_Init(glb[0], config);
        requires forall i{:trigger GLS_Next(glb[i], glb[i + 1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i + 1]);
        ensures |sb| == |glb|;
        ensures forall i :: 0 <= i < |sb| ==> sb[i].hosts == Collections__Maps2_s.mapdomain(glb[i].ls.servers); 
        ensures forall i :: 0 <= i < |sb| ==> sb[i].history == glb[i].history;
        ensures Service_Init(sb[0], Collections__Maps2_s.mapdomain(glb[0].ls.servers));
        ensures forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
    {
        if (|glb| == 1) {
            var ss := ServiceState'(Collections__Maps2_s.mapdomain(glb[0].ls.servers), glb[0].history);
            assert(GLS_Init(glb[0], config));
            assert(glb[0].history == [config[0]]);
            assert(forall e :: e in glb[0].ls.servers <==> e in config);
            assert(config[0] in glb[0].ls.servers);
            assert(config[0] in Collections__Maps2_s.mapdomain(glb[0].ls.servers));
            sb := [ss];
        }
        else {
            var ss := ServiceState'(Collections__Maps2_s.mapdomain(glb[|glb| - 1].ls.servers), glb[|glb| - 1].history);
            var prev_sb := GLSToSS(glb[0..|glb| - 1], config);
            assert(|prev_sb| == |glb| - 1);
            sb := prev_sb + [ss];
            var i := |glb| - 2;
            var s := glb[i];
            var ss_prev := sb[i];
            var s' := glb[i + 1];
            assert(ss.history == s'.history);
            assert(ss_prev.history == s.history);
            assert(ss.hosts == Collections__Maps2_s.mapdomain(s'.ls.servers));
            assert(ss_prev.hosts == Collections__Maps2_s.mapdomain(s.ls.servers));
            assert(GLS_Next(s, s'));
            assert(LS_Next(s.ls, s'.ls));
            LS_ServerInvariant(s.ls, s'.ls);
            assert(Collections__Maps2_s.mapdomain(s.ls.servers) == Collections__Maps2_s.mapdomain(s'.ls.servers));
            assert(ss.hosts == ss_prev.hosts);
            if (s.ls.environment.nextStep.LEnvStepHostIos? && s.ls.environment.nextStep.actor in s.ls.servers
               && NodeGrant(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
               && s.ls.servers[s.ls.environment.nextStep.actor].held && s.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF) {
                    GLS_ConfigInvariant(glb, config);
                    GLS_Seq_ServerInvariant(glb, config);
                    assert(s.ls.servers[s.ls.environment.nextStep.actor].config == config);
                    assert(forall e :: e in s.ls.servers <==> e in config);
                    assert(s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|] in config);
                    var new_hist := s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|];
                    assert(new_hist in s.ls.servers);
                    assert(new_hist in ss_prev.hosts);
                    assert(s'.history == s.history + [new_hist]);
                    assert(ss.history == ss_prev.history + [new_hist]);
                    assert(Service_Next(ss_prev, ss)); 
            }
            else {
                assert(s.history == s'.history);
                assert(ss.history == ss_prev.history);
            }           
        }
    }


    lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
        // requires |db| > 0;
        // requires DS_Init(db[0], config);
        // requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        // ensures  |db| == |sb|;
        // ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
        // ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        // ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
    {
        OnlyMarshallableData(db, config);
        var lb := DStoLS(config, db);
        var glb := LSToGLS(lb, config);
        assert(|glb| == |db|);
        assert(forall i :: 0 <= i < |glb| ==> forall m :: m in db[i].environment.sentPackets ==> AbstractifyConcretePacket(m) in glb[i].ls.environment.sentPackets);
        LockIsUnique(glb, config);
        GLS_Cor_Seq(db, glb, config);
        sb := GLSToSS(glb, config);
    }
}