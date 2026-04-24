{ pkgs }:  
  
{  
  deps = [  
    pkgs.zig  
    pkgs.gcc  
    pkgs.gnumake  
    pkgs.pkg-config  
    pkgs.futhark  
  ];  
  
  env = {  
    ZIG_GLOBAL_CACHE_DIR = "/tmp/zig-cache";  
  };  
}
