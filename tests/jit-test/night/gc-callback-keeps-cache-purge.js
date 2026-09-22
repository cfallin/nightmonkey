// The shell's setGCCallback replaces the engine's GC callback; the tier's
// inline caches must still be purged around a major GC.
function garbage() { var x; for (var i = 0; i < 100000; i++) x = { i: i }; }
setGCCallback({ action: "majorGC", depth: 1, phases: "both" });
garbage();
gc();
garbage();
setGCCallback({ action: "minorGC", phases: "begin" });
garbage();
gc();
garbage();
