#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(rustc::default_hash_types)]

use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::interpret::ConstValue;
use rustc_middle::mir::TerminatorKind::Goto;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Constant, ConstantKind, Field, LocalDecl, MirPass, Operand, Place,
    ProjectionElem, Rvalue, SourceInfo, Statement, StatementKind, Terminator,
};
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty;
use rustc_middle::ty::{GenericArg, TyCtxt};
use rustc_span::{sym, DUMMY_SP, Symbol};

pub struct Parallelism;

impl<'tcx> MirPass<'tcx> for Parallelism {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        println!("analysis auto parallelism in: {:?}", tcx.item_name(body.source.instance.def_id()));
        let parallel_result: FxHashMap<((u32, u32), (u32, u32)), bool> =
            find_func_parallel(&body, tcx);
        if parallel_result.len() > 1 {
            println!("unimplemented for more than two auto parallel functions");
            return;
        }

        for (((loc1, _), (loc2, _)), is_parallel) in parallel_result.iter() {
            if !is_parallel {
                continue;
            }
            let bb = BasicBlock::from_u32(*loc1);
            let bb2 = BasicBlock::from_u32(*loc2);
            if let TerminatorKind::Call { func, args, destination, target, .. } =
                body[bb].terminator().kind.clone()
            {
                if let TerminatorKind::Call {
                    func: func2,
                    args: args2,
                    destination: destination2,
                    target: target2,
                    ..
                } = body[bb2].terminator().kind.clone()
                {
                    let loc1 = (bb.as_u32(), body[bb].statements.len() as u32);
                    let loc2 = (bb2.as_u32(), body[bb2].statements.len() as u32);
                    if parallel_result.get(&(loc1, loc2)) != Some(&true) {
                        continue;
                    }
                    let (fn_id, subs) = if let ty::FnDef(fn_id, subs) = func.ty(body, tcx).kind() {
                        if tcx.get_attr(*fn_id, sym::parallel_func).is_none() {
                            continue;
                        } else {
                            assert_eq!(subs.len(), 0);
                            (*fn_id, *subs)
                        }
                    } else {
                        bug!("bad call")
                    };
                    let (fn_id2, subs2) =
                        if let ty::FnDef(fn_id, subs2) = func2.ty(body, tcx).kind() {
                            if tcx.get_attr(*fn_id, sym::parallel_func).is_none() {
                                continue;
                            } else {
                                assert_eq!(subs2.len(), 0);
                                (*fn_id, *subs2)
                            }
                        } else {
                            bug!("bad call")
                        };

                    assert_eq!(args.len(), 2);
                    assert_eq!(args2.len(), 2);

                    let args: Vec<_> = args.into_iter().map(|arg| {
                        let ty = arg.ty(body, tcx);
                        let local = body.local_decls.push(LocalDecl::new(ty, DUMMY_SP));
                        body[bb].statements.push(Statement {
                            source_info: SourceInfo::outermost(DUMMY_SP),
                            kind: StatementKind::Assign(Box::new((
                                Place::from(local),
                                Rvalue::Use(arg),
                            ))),
                        });
                        Operand::Move(Place::from(local))
                    }).collect();
                    let args2: Vec<_> = args2.into_iter().map(|arg| {
                        let ty = arg.ty(body, tcx);
                        let local = body.local_decls.push(LocalDecl::new(ty, DUMMY_SP));
                        body[bb2].statements.push(Statement {
                            source_info: SourceInfo::outermost(DUMMY_SP),
                            kind: StatementKind::Assign(Box::new((
                                Place::from(local),
                                Rvalue::Use(arg),
                            ))),
                        });
                        Operand::Move(Place::from(local))
                    }).collect();

                    let (arg1_0, arg1_1) = (args[0].ty(body, tcx), args[1].ty(body, tcx));
                    let (arg2_0, arg2_1) = (args2[0].ty(body, tcx), args2[1].ty(body, tcx));

                    let ret_ty1 = destination.ty(body, tcx).ty;
                    let ret_ty2 = destination2.ty(body, tcx).ty;

                    let fn_def1 = tcx.mk_fn_def(fn_id, subs);
                    let fn_def2 = tcx.mk_fn_def(fn_id2, subs2);

                    let to_substs1 = tcx.mk_substs(
                        [
                            GenericArg::from(arg1_0),
                            GenericArg::from(arg1_1),
                            GenericArg::from(ret_ty1),
                            GenericArg::from(fn_def1),
                        ]
                        .into_iter(),
                    );
                    let to_substs2 = tcx.mk_substs(
                        [
                            GenericArg::from(arg2_0),
                            GenericArg::from(arg2_1),
                            GenericArg::from(ret_ty2),
                            GenericArg::from(fn_def2),
                        ]
                        .into_iter(),
                    );

                    let fn_arg1 = Operand::Constant(Box::new(Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: ConstantKind::Val(
                            ConstValue::ZeroSized,
                            fn_def1,
                        ),
                    }));
                    let fn_arg2 = Operand::Constant(Box::new(Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: ConstantKind::Val(
                            ConstValue::ZeroSized,
                            fn_def2,
                        ),
                    }));

                    let to_once_call_arg2_id =
                        tcx.require_lang_item(LangItem::ToOnceCallArg2, None);

                    let to_once_call_ty1 = tcx.mk_fn_def(to_once_call_arg2_id, to_substs1);
                    let to_once_call_ty2 = tcx.mk_fn_def(to_once_call_arg2_id, to_substs2);

                    let to_once_call_func1 = Operand::Constant(Box::new(Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: ConstantKind::Val(
                            ConstValue::ZeroSized,
                            to_once_call_ty1,
                        ),
                    }));
                    let to_once_call_func2 = Operand::Constant(Box::new(Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: ConstantKind::Val(
                            ConstValue::ZeroSized,
                            to_once_call_ty2,
                        ),
                    }));

                    let des_ty = tcx.fn_sig(to_once_call_arg2_id).skip_binder().output();

                    let des_ty1 = if let ty::Opaque(id, _sub) = des_ty.kind() {
                        tcx.mk_opaque(*id, to_substs1)
                    } else {
                        bug!("bad des ty: {:?}", des_ty)
                    };
                    let des_ty2 = if let ty::Opaque(id, _sub) = des_ty.kind() {
                        tcx.mk_opaque(*id, to_substs2)
                    } else {
                        bug!("bad des ty: {:?}", des_ty)
                    };

                    let once_call_des1 = body.local_decls.push(LocalDecl::new(des_ty1, DUMMY_SP));
                    let once_call_des2 = body.local_decls.push(LocalDecl::new(des_ty2, DUMMY_SP));

                    let to_once_call_des1 =
                        Place::from(once_call_des1);
                    let to_once_call_des2 =
                        Place::from(once_call_des2);

                    let once_call_block1 = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    body[bb].terminator_mut().kind = Goto { target: target.unwrap() };

                    body[bb2].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageLive(once_call_des1),
                    });
                    body[bb2].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageLive(once_call_des2),
                    });
                    body[bb2].terminator_mut().kind = TerminatorKind::Call {
                        func: to_once_call_func1,
                        args: vec![fn_arg1, args[0].clone(), args[1].clone()],
                        destination: to_once_call_des1,
                        target: Some(once_call_block1),
                        cleanup: None,
                        from_hir_call: false,
                        fn_span: DUMMY_SP,
                    };

                    let once_call_block2 = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    body[once_call_block1].terminator = Some(Terminator {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: TerminatorKind::Call {
                            func: to_once_call_func2,
                            args: vec![fn_arg2, args2[0].clone(), args2[1].clone()],
                            destination: to_once_call_des2,
                            target: Some(once_call_block2),
                            cleanup: None,
                            from_hir_call: false,
                            fn_span: DUMMY_SP,
                        },
                    });

                    let join_call_id = tcx.require_lang_item(LangItem::RayonJoin, None);
                    let join_call_ty = tcx.mk_fn_def(
                        join_call_id,
                        tcx.mk_substs(
                            [
                                GenericArg::from(ret_ty1),
                                GenericArg::from(ret_ty2),
                                GenericArg::from(des_ty1),
                                GenericArg::from(des_ty2),
                            ]
                            .into_iter(),
                        ),
                    );
                    let join_call_func = Operand::Constant(Box::new(Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: ConstantKind::Val(
                            ConstValue::ZeroSized,
                            join_call_ty,
                        ),
                    }));

                    let join_ret_ty = tcx.mk_tup([ret_ty1, ret_ty2].into_iter());
                    let join_ret = body.local_decls.push(LocalDecl::new(join_ret_ty, DUMMY_SP));

                    let join_block = body.basic_blocks_mut().push(BasicBlockData::new(None));
                    body[once_call_block2].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageLive(join_ret),
                    });
                    body[once_call_block2].terminator = Some(Terminator {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: TerminatorKind::Call {
                            func: join_call_func,
                            args: vec![
                                Operand::Move(to_once_call_des1),
                                Operand::Move(to_once_call_des2),
                            ],
                            destination: Place::from(join_ret),
                            target: Some(join_block),
                            cleanup: None,
                            from_hir_call: false,
                            fn_span: DUMMY_SP,
                        },
                    });

                    body[join_block].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::Assign(Box::new((
                            destination.clone(),
                            Rvalue::Use(Operand::Move(tcx.mk_place_elem(
                                Place::from(join_ret),
                                ProjectionElem::Field(Field::from_u32(0), ret_ty1),
                            ))),
                        ))),
                    });
                    body[join_block].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::Assign(Box::new((
                            destination2.clone(),
                            Rvalue::Use(Operand::Move(tcx.mk_place_elem(
                                Place::from(join_ret),
                                ProjectionElem::Field(Field::from_u32(1), ret_ty2),
                            ))),
                        ))),
                    });

                    body[join_block].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageDead(once_call_des1),
                    });
                    body[join_block].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageDead(once_call_des2),
                    });
                    body[join_block].statements.push(Statement {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: StatementKind::StorageDead(join_ret),
                    });
                    body[join_block].terminator = Some(Terminator {
                        source_info: SourceInfo::outermost(DUMMY_SP),
                        kind: Goto { target: target2.unwrap() },
                    });
                }
            }
        }
    }
}

//chunmiao added parts
//*************************************************************************************************************************

use crepe::crepe;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::process::Command;

crepe! { //----按照原先写的datalog文件，写出下面这些规则
    // @input
    // struct Edge<'a>(&'a str, &'a str);

    @input
    struct loan_issued_at<'a>(&'a str, &'a str, &'a str);  //loan_issued_at(Origin:symbol, Loan:symbol, Point:symbol)

    @input
    struct loan_killed_at<'a>(&'a str, &'a str);     //loan_killed_at(Loan:symbol, Point:symbol)

    @input
    struct loan_invalidated_at<'a>(&'a str, &'a str); //loan_invalidated_at(Point:symbol, Loan:symbol)

    @input
    struct var_defined_at<'a>(&'a str, &'a str); //var_defined_at(Variable:symbol, Point:symbol)

    @input
    struct var_used_at<'a>(&'a str, &'a str);   //var_used_at(Variable:symbol, Point:symbol)

    @output
    struct in_set<'a>(&'a str, &'a str); //in_set(Variable:symbol, Point:symbol)

    @output
    struct var_loan<'a>(&'a str, &'a str); //var_loan(Variable:symbol, Loan:symbol)

    var_loan(var,loan) <- loan_issued_at(_, loan, point), var_defined_at(var, point);

    @output
    struct except1_var<'a>(&'a str, &'a str); //except1_var(var:symbol, point:symbol)
    except1_var(var, point) <- loan_invalidated_at(point, loan), var_loan(var,loan);

    @input
    struct function_call_point<'a>(&'a str); //function_call_point(point:symbol)

    in_set(var, point) <- var_used_at(var, point), function_call_point(point), !except1_var(var, point);

    @output
    struct except2_var<'a>(&'a str, &'a str); // except2_var(var:symbol, point:symbol)
    except2_var(var, point) <- loan_killed_at(loan, point), var_loan(var,loan), function_call_point(point);

    @output
    struct out_set<'a>(&'a str, &'a str); //out_set(Variable:symbol, Point:symbol)
    out_set(var, point) <- var_defined_at(var, point), function_call_point(point), !except2_var(var, point);

    @output
    struct var_relates<'a>(&'a str, &'a str); //var_relates(var1:symbol, var2:symbol)
    var_relates(var1, var2) <- var_defined_at(var1, point), var_used_at(var2, point);
    var_relates(var1, var3) <- var_relates(var1, var2), var_relates(var2, var3), !user_var(var2);
    var_relates(var1, var1) <- var_defined_at(var1, _);
    var_relates(var1, var1) <- var_used_at(var1, _);

    @input
    struct temp_var_user_var_name_mapping<'a>(&'a str, &'a str); //temp_var_user_var_name_mapping(temp_var:symbol, user_var:symbol)

    @input
    struct closure_temp_var_mapping<'a>(&'a str, &'a str); //closure_temp_var_mapping(closure:symbol, temp_var:symbol)

    @output
    struct user_var<'a>(&'a str); //user_var(var:symbol)
    user_var(temp_var) <- temp_var_user_var_name_mapping(temp_var, _);
    user_var(temp_var) <- closure_temp_var_mapping(_,temp_var);

    @input
    struct unmut_var_type_mapping<'a>(&'a str, &'a str); //unmut_var_type_mapping(temp_var:symbol,type:symbol)

    @output
    struct no_track_to_user_var<'a>(&'a str); //no_track_to_user_var(var:symbol)
    no_track_to_user_var(temp_var) <- unmut_var_type_mapping(temp_var, "()");

    @output
    struct final_in_set<'a>(&'a str, &'a str); //final_in_set(var:symbol, point:symbol)
    final_in_set(user_var_name, point) <- in_set(temp_var, point), user_var(user_var_name), var_relates(temp_var,user_var_name),!no_track_to_user_var(temp_var);

    @output
    struct var_name_mapping<'a>(&'a str, &'a str); //var_name_mapping(user_var:symbol, varName:symbol)
    var_name_mapping(temp_var,user_var_name) <- temp_var_user_var_name_mapping(temp_var,user_var_name);
    var_name_mapping(temp_var,closure) <- closure_temp_var_mapping(closure, temp_var);

    @output
    struct final_in_varNameset<'a>(&'a str); //final_in_varNameset(varName:symbol)
    final_in_varNameset(varName) <- final_in_set(user_var_name, _), var_name_mapping(user_var_name, varName);

    @input
    struct mut_var_type_mapping<'a>(&'a str, &'a str); //mut_var_type_mapping(temp_var:symbol,type:symbol)

    @output
    struct mut_loan_var<'a>(&'a str); //mut_loan_var(var:symbol)
    mut_loan_var(temp_var) <- mut_var_type_mapping(temp_var,_), var_defined_at(temp_var,point), loan_issued_at(_,_,point);

    @output
    struct final_out_set<'a>(&'a str, &'a str); //final_out_set(var:symbol, point:symbol)
    final_out_set(user_var_name, point) <- out_set(temp_var, point), user_var(user_var_name), var_relates(temp_var,user_var_name),!no_track_to_user_var(temp_var), !user_var(temp_var);
    final_out_set(temp_var, point) <- out_set(temp_var, point), user_var(temp_var);
    final_out_set(user_var_name, point) <- final_in_set(user_var_name,point), loan_issued_at(_,loan,point1), var_used_at(user_var_name,point1), var_loan(temp_var,loan), mut_loan_var(temp_var);

    @output
    struct final_out_varNameset<'a>(&'a str); //final_out_varNameset(varName:symbol)
    final_out_varNameset(varName) <- final_out_set(user_var_name, _), var_name_mapping(user_var_name, varName);


    // @output
    // struct Reachable<'a>(&'a str, &'a str);

    // Reachable(x, y) <- Edge(x, y);
    // Reachable(x, z) <- Edge(x, y), Reachable(y, z);
}

//Chunmiao added this function to get a hashmap for parallelization among functions
fn find_func_parallel<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<((u32, u32), (u32, u32)), bool> {
    let mut func_parallel_table: FxHashMap<((u32, u32), (u32, u32)), bool> = FxHashMap::default();

    let func_calls: Vec<(u32, u32, Symbol)> = body
        .basic_blocks
        .iter()
        .enumerate()
        .filter_map(|(location, data)| {
            if let TerminatorKind::Call { func, .. } = &data.terminator().kind {
                if let ty::FnDef(defid, _) = func.ty(body, tcx).kind() {
                    if tcx.get_attr(*defid, sym::parallel_func).is_some() {
                        Some((location as u32, data.statements.len() as u32, tcx.item_name(*defid)))
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    for (block_id1, stmt_no1, func1) in func_calls.iter() {
        for (block_id2, stmt_no2, func2) in func_calls.iter() {
            if block_id1 < block_id2 {
                let source = body.source;
                let item_name = tcx.def_path(source.def_id()).to_filename_friendly_no_crate();
                let prefix_path = format!("{}/{}/", tcx.sess.opts.unstable_opts.nll_facts_dir, &item_name);
                let mir_path = format!(
                    "{}/{}.{}.-------.pre_parallelization.0.mir",
                    tcx.sess.opts.unstable_opts.dump_mir_dir,
                    tcx.crate_name(source.def_id().krate),
                    &item_name
                );

                let is_parallel = whether_two_func_parallel(
                    &prefix_path,
                    &mir_path,
                    *block_id1,
                    *stmt_no1,
                    *block_id2,
                    *stmt_no2,
                );

                func_parallel_table.insert(
                    ((*block_id1, *stmt_no1), (*block_id2, *stmt_no2)), is_parallel,
                );

                if is_parallel {
                    println!("{:?}_{:?} with {:?}_{:?} can run in parallel:", block_id1, func1, block_id2, func2);
                }
            }
        }
    }

    func_parallel_table
}

fn whether_two_func_parallel(
    prefix_path: &String,
    mir_path: &String,
    block_id1: u32,
    stmt_no1: u32,
    block_id2: u32,
    stmt_no2: u32,
) -> bool {
    let (block1_in, block1_out) = find_func_inout(prefix_path, mir_path, block_id1, stmt_no1);
    let (block2_in, block2_out) = find_func_inout(prefix_path, mir_path, block_id2, stmt_no2);

    //println!("bb{} in:{:?}, out:{:?}", block_id1, block1_in, block1_out);
    //println!("bb{} in:{:?}, out:{:?}", block_id2, block2_in, block2_out);

    let mut tag = true;
    //if intersection occurs, then this two blocks cannot be paralled
    if block1_in.intersection(&block2_out).count() > 0
        || block2_in.intersection(&block1_out).count() > 0
    {
        tag = false;
    }

    tag
}

fn find_func_inout(
    prefix_path: &String,
    mir_path: &String,
    block_id: u32,
    stmt_no: u32,
) -> (FxHashSet<String>, FxHashSet<String>) {
    let mut block_in: FxHashSet<String> = FxHashSet::default();
    let mut block_out: FxHashSet<String> = FxHashSet::default();

    let mut runtime = Crepe::new();

    //先用quicksort函数测试

    //从facts文件中读入
    // let _polonius_facts_vec = vec!["closure_temp_var_mapping","function_call_point","loan_invalidated_at",
    //                       "loan_issued_at","loan_killed_at","mut_var_type_mapping",
    //                       "temp_var_user_var_name_mapping","unmut_var_type_mapping",
    //                       "var_defined_at", "var_used_at"];

    // let prefix_path = "/Users/lichunmiao/trytry/nll-facts/quick_sort/";

    // 需指定的facts文件的路径
    // 1. polonius生成的facts
    // 2. 从MIR中爬下来的facts
    // 3. 指定的blockID node的facts (已经直接指定, 即function_call_point中的内容)

    //对mir文件执行python3的操作，其中需要指定mir文件的地址和facts的地址(因为要把生成的facts挪到find_prime文件夹下)
    let status = Command::new("python3")
        .arg("extract_input.py")
        .arg(mir_path)
        .arg(prefix_path)
        .status()
        .expect("failed to execute process");
    // println!("process finished with: {status}");
    assert!(status.success());

    //-----------------------------------------closure_temp_var_mapping-----------------------//
    let mut file_path = prefix_path.to_string() + "closure_temp_var_mapping.facts";

    let mut file = File::open(file_path).unwrap();
    let mut reader = BufReader::new(file);

    let mut closure_temp_var_mapping_vec = Vec::new();
    let mut closure_temp_var_mapping_array: Vec<closure_temp_var_mapping<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        closure_temp_var_mapping_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in closure_temp_var_mapping_vec.iter() {
        // &String -> &str
        closure_temp_var_mapping_array.push(closure_temp_var_mapping(&val1, &val2));
    }

    runtime.extend(closure_temp_var_mapping_array);

    //-------------------------------------function_call_point---------------------------//

    /*function_call_point直接可以拿到*/
    /*  "Mid(bb17[8])"  */

    // file_path = prefix_path.to_string() + "function_call_point.facts";
    // file = File::open(file_path).unwrap();
    // reader = BufReader::new(file);

    // let mut function_call_point_vec = Vec::new();
    let mut function_call_point_array: Vec<function_call_point<'_>> = Vec::new();

    let blockId_string = format!("\"Mid(bb{}[{}])\"", block_id, stmt_no);
    //  .to_string();

    // for line in reader.lines() {
    //     let x = line.unwrap();
    //     let ll:Vec<&str> = x.split("\t").collect();
    //     function_call_point_vec.push((ll[0].to_string()));
    // };

    // &String -> &str
    function_call_point_array.push(function_call_point(&blockId_string));

    runtime.extend(function_call_point_array);
    //------------------------------------------loan_invalidated_at----------------------

    file_path = prefix_path.to_string() + "loan_invalidated_at.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut loan_invalidated_at_vec = Vec::new();
    let mut loan_invalidated_at_array: Vec<loan_invalidated_at<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        loan_invalidated_at_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in loan_invalidated_at_vec.iter() {
        // &String -> &str
        loan_invalidated_at_array.push(loan_invalidated_at(&val1, &val2));
    }

    runtime.extend(loan_invalidated_at_array);

    //--------------------------------loan_issued_at--------------------------------

    file_path = prefix_path.to_string() + "loan_issued_at.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut loan_issued_at_vec = Vec::new();
    let mut loan_issued_at_array: Vec<loan_issued_at<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        // println!("{} {} {}", ll[0], ll[1], ll[2]);
        loan_issued_at_vec.push((ll[0].to_string(), ll[1].to_string(), ll[2].to_string()));
    }

    for (val1, val2, val3) in loan_issued_at_vec.iter() {
        // &String -> &str
        loan_issued_at_array.push(loan_issued_at(&val1, &val2, &val3));
    }

    runtime.extend(loan_issued_at_array);

    //--------------------------------loan_killed_at--------------------------------
    file_path = prefix_path.to_string() + "loan_killed_at.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut loan_killed_at_vec = Vec::new();
    let mut loan_killed_at_array: Vec<loan_killed_at<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        loan_killed_at_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in loan_invalidated_at_vec.iter() {
        // &String -> &str
        loan_killed_at_array.push(loan_killed_at(&val1, &val2));
    }

    runtime.extend(loan_killed_at_array);

    //--------------------------------mut_var_type_mapping--------------------------------
    file_path = prefix_path.to_string() + "mut_var_type_mapping.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut mut_var_type_mapping_vec = Vec::new();
    let mut mut_var_type_mapping_array: Vec<mut_var_type_mapping<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        mut_var_type_mapping_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in mut_var_type_mapping_vec.iter() {
        // &String -> &str
        mut_var_type_mapping_array.push(mut_var_type_mapping(&val1, &val2));
    }

    runtime.extend(mut_var_type_mapping_array);

    //--------------------------------temp_var_user_var_name_mapping--------------------------------
    file_path = prefix_path.to_string() + "temp_var_user_var_name_mapping.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut temp_var_user_var_name_mapping_vec = Vec::new();
    let mut temp_var_user_var_name_mapping_array: Vec<temp_var_user_var_name_mapping<'_>> =
        Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        temp_var_user_var_name_mapping_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in temp_var_user_var_name_mapping_vec.iter() {
        // &String -> &str
        temp_var_user_var_name_mapping_array.push(temp_var_user_var_name_mapping(&val1, &val2));
    }

    runtime.extend(temp_var_user_var_name_mapping_array);

    //------------------------------unmut_var_type_mapping--------------------------------
    file_path = prefix_path.to_string() + "unmut_var_type_mapping.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut unmut_var_type_mapping_vec = Vec::new();
    let mut unmut_var_type_mapping_array: Vec<unmut_var_type_mapping<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        unmut_var_type_mapping_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in unmut_var_type_mapping_vec.iter() {
        // &String -> &str
        unmut_var_type_mapping_array.push(unmut_var_type_mapping(&val1, &val2));
    }

    runtime.extend(unmut_var_type_mapping_array);

    //------------------------------var_defined_at--------------------------------
    file_path = prefix_path.to_string() + "var_defined_at.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut var_defined_at_vec = Vec::new();
    let mut var_defined_at_array: Vec<var_defined_at<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        var_defined_at_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in var_defined_at_vec.iter() {
        // &String -> &str
        var_defined_at_array.push(var_defined_at(&val1, &val2));
    }

    runtime.extend(var_defined_at_array);

    //--------------------------------var_used_at--------------------------------
    file_path = prefix_path.to_string() + "var_used_at.facts";
    file = File::open(file_path).unwrap();
    reader = BufReader::new(file);

    let mut var_used_at_vec = Vec::new();
    let mut var_used_at_array: Vec<var_used_at<'_>> = Vec::new();

    for line in reader.lines() {
        let x = line.unwrap();
        let ll: Vec<&str> = x.split("\t").collect();
        var_used_at_vec.push((ll[0].to_string(), ll[1].to_string()));
    }

    for (val1, val2) in var_used_at_vec.iter() {
        // &String -> &str
        var_used_at_array.push(var_used_at(&val1, &val2));
    }

    runtime.extend(var_used_at_array);

    // runtime.extend(&[Edge("1", "2"), Edge("2", "3")]);

    //计算输出

    let (_a, _b, _c, _d, _e, _f, _g, _h, _i, _j, k, _l, _m, n) = runtime.run();

    // println!("var_relates is: ");
    // for var_relates(x,y) in f {
    //     println!(" {} {}", x,y);
    // }

    // println!("in_set is: ");
    // for in_set(x,y) in a {
    //     println!(" {} {}", x,y);
    // }

    // println!("no_track_to_user is: ");
    // for no_track_to_user_var(x) in h {
    //     println!(" {} ", x);
    // }

    // println!("final_in_set is: ");
    // for final_in_set(x,y) in i {
    //     println!(" {} {}", x,y);
    // }

    //**************************************************************** */
    // println!("final in varName is: ");
    for final_in_varNameset(x) in k {
        // println!(" {} ", x);
        block_in.insert(x.to_string());
    }

    // println!("final out varName is: ");
    for final_out_varNameset(x) in n {
        // println!(" {} ", x);
        block_out.insert(x.to_string());
    }
    //**************************************************************** */
    // block_in.insert("a");
    // block_in.insert("b");
    // block_in.insert("mid");

    // if block_id == 17  {block_out.insert("lo");}
    // if block_id == 19  {block_out.insert("hi");}

    println!("For block is {}, block in is {:?}", block_id, block_in);
    println!("                 block out is {:?}", block_out);

    (block_in, block_out)
}

//*************************************************************************************************************************
