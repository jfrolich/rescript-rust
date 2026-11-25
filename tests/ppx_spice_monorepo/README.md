# Derived code in a package of a monorepo

A root package and one package below it (`packages/shared`) that derives
codecs. `packages/shared/src/shared/Layout.res` has a derived type in a nested
module, derived records and variants at the top level, and a match that can
fail: its `Match_failure` names a place in the source, so a compile without
location tables is abandoned and the unit is compiled again with them.

Built from this directory with `RESCRIPT_DERIVED_PATH=check`, every unit that
has a plan must be compiled both ways and compared, also the one that was
compiled again. The dependency is resolved through `node_modules`, which is not
checked in:

    mkdir -p node_modules/@derived-code-monorepo
    ln -s ../../packages/shared node_modules/@derived-code-monorepo/shared
    RESCRIPT_DERIVED_PATH=check rescript build
