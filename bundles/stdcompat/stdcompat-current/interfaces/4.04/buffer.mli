type t
val create : int -> t
val contents : t -> string
val to_bytes : t -> bytes
val sub : t -> int -> int -> string
val blit : t -> int -> bytes -> int -> int -> unit
val nth : t -> int -> char
val length : t -> int
val clear : t -> unit
val reset : t -> unit
val add_char : t -> char -> unit
val add_string : t -> string -> unit
val add_bytes : t -> bytes -> unit
val add_substring : t -> string -> int -> int -> unit
val add_subbytes : t -> bytes -> int -> int -> unit
val add_substitute : t -> (string -> string) -> string -> unit
val add_buffer : t -> t -> unit
val add_channel : t -> in_channel -> int -> unit
val output_buffer : out_channel -> t -> unit
