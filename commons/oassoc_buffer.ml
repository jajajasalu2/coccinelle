open Common
open Oassoc
open Oassocb
open Osetb


(* !!take care!!: this class does side effect, not a pure oassoc *)
(*  limit number of entries, and erase all (then better do a ltu) *)
(* class ['a,'b] oassoc_cache cache cached max =  *)
(*   object(o) *)
(*     inherit ['a,'b] oassoc *)
(*  *)
(*     val full = ref 0 *)
(*     val max = max *)
(*     val cache = cache *)
(*     val cached = cached *)
(*     val lru = TODO *)
(*        *)
(*     val data = Hashtbl.create 100 *)
(*  *)
(*     method empty = raise Todo *)
(*     method add (k,v) = (Hashtbl.add data k v; o) *)
(*     method iter f = cached#iter f *)
(*     method view = raise Todo *)
(*  *)
(*     method del (k,v) = (cache#del (k,v); cached#del (k,v); o) *)
(*     method mem e = raise Todo *)
(*     method null = raise Todo *)
(*  *)
(*     method assoc k = Hashtbl.find data k *)
(*     method delkey k = (cache#delkey (k,v); cached#del (k,v); o) *)
(* end    *)

(* TODO another cache that behave as in lfs1, every 100 operation do a flush *)
(* can not make it pure, cos the assoc have side effect on the cache *)
class ['a,'b] oassoc_buffer max cached = 
  object(o)
    inherit ['a,'b] oassoc

    val counter = ref 0
    val cache = ref (new oassocb []) 
    val dirty = ref (new osetb Setb.empty)
    val wrapped = ref cached

    method private myflush = 
      (!dirty#iter (fun k -> wrapped := !wrapped#add (k, !cache#assoc k));
       dirty := (new osetb Setb.empty);
       cache := (new oassocb []);
       counter := 0;
      )
    method generic = o#myflush
        
    method empty = raise Todo
    method add (k,v) = 
      (cache := !cache#add (k,v);
       dirty := !dirty#add k;
       incr counter;
       if !counter > max then o#myflush;
       o)

    method iter f = 
      (* bugfix: have to flush !!! *)
      (o#myflush;
      !wrapped#iter f
      )

    method length = 
      o#myflush;
      !wrapped#length


    method view = raise Todo

    method del (k,v) = 
      (cache := !cache#del (k,v); 
       (* TODO as for delkey, do a try over wrapped *)
       wrapped := !wrapped#del (k,v); 
       dirty := !dirty#del k;
       o)
    method mem e = raise Todo
    method null = raise Todo

    method assoc k = 
      (try !cache#assoc k with
        Not_found -> 
          let v = !wrapped#assoc k in (* may launch Not_found, but this time, dont catch it *)
          (cache := !cache#add (k,v);
           (* otherwise can use too much mem *)
           incr counter;
           if !counter > max then o#myflush;
           v)
      )
          
    method delkey k = 
      (cache := !cache#delkey k; 
       (*  sometimes have not yet flushed, so may not be yet in, (could also flush in place of doing try) *)
       (* TODO would be better to see if was in cache (in case mean that perhaps not flushed and do try *)
       (*  and in other case just cos del (without try) cos forcement flushed ou was an error *)
       (try wrapped := !wrapped#delkey k with Not_found -> ()); 
       dirty := !dirty#del k;
       o)
end     
