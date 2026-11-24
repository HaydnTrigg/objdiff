use objdiff_core::{diff, diff::display::SymbolFilter, obj};

mod common;

#[test]
#[cfg(feature = "x86")]
fn read_x86() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/staticdebug.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
    let symbol_idx = obj.symbols.iter().position(|s| s.name == "?PrintThing@@YAXXZ").unwrap();
    let diff = diff::code::no_diff_code(&obj, symbol_idx, &diff_config).unwrap();
    insta::assert_debug_snapshot!(diff.instruction_rows);
    let output = common::display_diff(&obj, &diff, symbol_idx, &diff_config);
    insta::assert_snapshot!(output);
}

#[test]
#[cfg(feature = "x86")]
fn read_x86_combine_sections() {
    let diff_config = diff::DiffObjConfig {
        combine_data_sections: true,
        combine_text_sections: true,
        ..Default::default()
    };
    let obj =
        obj::read::parse(include_object!("data/x86/rtest.obj"), &diff_config, diff::DiffSide::Base)
            .unwrap();
    insta::assert_debug_snapshot!(obj.sections);
}

#[test]
#[cfg(feature = "x86")]
fn read_x86_64() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86_64/vs2022.o"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
    let symbol_idx =
        obj.symbols.iter().position(|s| s.name == "?Dot@Vector@@QEAAMPEAU1@@Z").unwrap();
    let diff = diff::code::no_diff_code(&obj, symbol_idx, &diff_config).unwrap();
    insta::assert_debug_snapshot!(diff.instruction_rows);
    let output = common::display_diff(&obj, &diff, symbol_idx, &diff_config);
    insta::assert_snapshot!(output);
}

#[test]
#[cfg(feature = "x86")]
fn display_section_ordering() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/basenode.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    let obj_diff =
        diff::diff_objs(Some(&obj), None, None, &diff_config, &diff::MappingConfig::default())
            .unwrap()
            .left
            .unwrap();
    let section_display =
        diff::display::display_sections(&obj, &obj_diff, SymbolFilter::None, false, false, false);
    insta::assert_debug_snapshot!(section_display);
}

#[test]
#[cfg(feature = "x86")]
fn read_x86_jumptable() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/jumptable.o"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
    let symbol_idx = obj.symbols.iter().position(|s| s.name == "?test@@YAHH@Z").unwrap();
    let diff = diff::code::no_diff_code(&obj, symbol_idx, &diff_config).unwrap();
    insta::assert_debug_snapshot!(diff.instruction_rows);
    let output = common::display_diff(&obj, &diff, symbol_idx, &diff_config);
    insta::assert_snapshot!(output);
}

// Inferred size of functions should ignore symbols with specific prefixes
#[test]
#[cfg(feature = "x86")]
fn read_x86_local_labels() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/local_labels.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
}

#[test]
#[cfg(feature = "x86")]
fn read_x86_indirect_table() {
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/indirect_table.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
    let symbol_idx = obj.symbols.iter().position(|s| s.name == "?process@@YAHHHH@Z").unwrap();
    let diff = diff::code::no_diff_code(&obj, symbol_idx, &diff_config).unwrap();
    insta::assert_debug_snapshot!(diff.instruction_rows);
    let output = common::display_diff(&obj, &diff, symbol_idx, &diff_config);
    insta::assert_snapshot!(output);
}

#[test]
#[cfg(feature = "x86")]
fn read_delphi_omf() {
    // Delphi 6 `dcc32 -JP` output for data/x86/delphi_probe.pas
    let diff_config = diff::DiffObjConfig::default();
    let obj = obj::read::parse(
        include_object!("data/x86/delphi_probe.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    insta::assert_debug_snapshot!(obj);
    let symbol_idx = obj.symbols.iter().position(|s| s.name == "@Describe$qqrp6TProbe").unwrap();
    let diff = diff::code::no_diff_code(&obj, symbol_idx, &diff_config).unwrap();
    let output = common::display_diff(&obj, &diff, symbol_idx, &diff_config);
    insta::assert_snapshot!(output);
}

// Logical diff: a single instruction moved past instructions it does not depend on matches;
// x87 instructions keep their order, and moves past a use of the moved register or of esp do
// not match (data/x86/logical_move/*.c)
#[test]
#[cfg(feature = "x86")]
fn diff_x86_logical_move() {
    let diff_config = diff::DiffObjConfig {
        function_reloc_diffs_name_address: false,
        function_reloc_diffs_logical: true,
        ..Default::default()
    };
    let target = obj::read::parse(
        include_object!("data/x86/logical_move/target.obj"),
        &diff_config,
        diff::DiffSide::Target,
    )
    .unwrap();
    let base = obj::read::parse(
        include_object!("data/x86/logical_move/base.obj"),
        &diff_config,
        diff::DiffSide::Base,
    )
    .unwrap();
    let result = diff::diff_objs(
        Some(&target),
        Some(&base),
        None,
        &diff_config,
        &diff::MappingConfig::default(),
    )
    .unwrap();
    let left = result.left.unwrap();
    let percent = |name: &str| {
        let idx = target.symbols.iter().position(|s| s.name == name).unwrap();
        left.symbols[idx].match_percent.unwrap()
    };
    assert_eq!(percent("_moved"), 100.0);
    assert!(percent("_fpu_order") < 100.0);
    assert!(percent("_dependent") < 100.0);
    assert!(percent("_stack") < 100.0);
}
