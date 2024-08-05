part of 'use_widget_ref_synchronously_rule.dart';

class _Visitor extends RecursiveAstVisitor<void> {
  _Visitor();

  final nodes = <SimpleIdentifier>[];

  @override
  void visitCompilationUnit(CompilationUnit node) {
    for (final declaration in node.declarations) {
      if (declaration is ClassDeclaration) {
        final type = declaration.extendsClause?.superclass.type;
        if (isWidgetOrSubclass(type) || isWidgetStateOrSubclass(type)) {
          declaration.visitChildren(this);
        }
      }
    }
  }

  @override
  void visitBlockFunctionBody(BlockFunctionBody node) {
    // if (node.toString().startsWith('async {MediaQue')) {
    //   print((((node.block.statements[4] as ExpressionStatement).expression
    //           as MethodInvocation)
    //       .target as SimpleIdentifier)
    //       .);
    // }
    if (!node.isAsynchronous) {
      return node.visitChildren(this);
    }
    final visitor = _AsyncSetStateVisitor();
    node.visitChildren(visitor);
    nodes.addAll(visitor.nodes);
  }
}

class _AsyncSetStateVisitor extends RecursiveAstVisitor<void> {
  _AsyncSetStateVisitor();

  MountedFact mounted = true.asFact();
  bool inControlFlow = false;
  bool inAsync = true;

  bool get isMounted => mounted.value ?? false;
  final nodes = <SimpleIdentifier>[];

  @override
  void visitAwaitExpression(AwaitExpression node) {
    mounted = false.asFact();
    super.visitAwaitExpression(node);
  }

  @override
  void visitAssertStatement(AssertStatement node) {
    final newMounted = _extractMountedCheck(node.condition);
    mounted = newMounted.or(mounted);
    super.visitAssertStatement(node);
  }

  @override
  void visitMethodInvocation(MethodInvocation node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    if (!isMounted &&
        node.realTarget != null &&
        _isWidgetRef(node.realTarget!.staticType, skipNullable: true)) {
      nodes.add(node.methodName);
    }

    super.visitMethodInvocation(node);
  }

  // @override
  // void visitPrefixedIdentifier(PrefixedIdentifier node) {
  //   print('visitPrefixedIdentifier($node, inAsync: $inAsync)');
  //   if (!inAsync) {
  //     return node.visitChildren(this);
  //   }

  //   if (!isMounted &&
  //       _isWidgetRef(node.prefix.staticType, skipNullable: true)) {
  //     nodes.add(node.identifier);
  //   }

  //   super.visitPrefixedIdentifier(node);
  // }

  bool _isWidgetRef(DartType? type, {bool skipNullable = false}) {
    if (type is! InterfaceType) {
      return false;
    }
    if (skipNullable && type.nullabilitySuffix == NullabilitySuffix.question) {
      return false;
    }

    return _isExactly(
      type.element,
      Uri.parse('package:flutter_riverpod/src/consumer.dart'),
      'WidgetRef',
    );
  }

  bool _isExactly(InterfaceElement element, Uri uri, String type) =>
      element.source.uri == uri && element.name == type;

  @override
  void visitIfStatement(IfStatement node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    // ignore: deprecated_member_use
    node.condition.accept(this);

    // ignore: deprecated_member_use
    final newMounted = _extractMountedCheck(node.condition);
    mounted = newMounted.or(mounted);

    final beforeThen = mounted;
    node.thenStatement.visitChildren(this);
    final afterThen = mounted;

    var elseDiverges = false;
    final elseStatement = node.elseStatement;
    if (elseStatement != null) {
      elseDiverges = _blockDiverges(
        elseStatement,
        allowControlFlow: inControlFlow,
      );
      mounted = _tryInvert(newMounted).or(mounted);
      elseStatement.visitChildren(this);
    }

    if (_blockDiverges(node.thenStatement, allowControlFlow: inControlFlow)) {
      mounted = _tryInvert(newMounted).or(beforeThen);
    } else if (elseDiverges) {
      mounted = beforeThen != afterThen
          ? afterThen
          // ignore: deprecated_member_use
          : _extractMountedCheck(node.condition, permitAnd: false);
    }
  }

  @override
  void visitWhileStatement(WhileStatement node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    node.condition.accept(this);

    final oldMounted = mounted;
    final newMounted = _extractMountedCheck(node.condition);
    mounted = newMounted.or(mounted);
    final oldInControlFlow = inControlFlow;
    inControlFlow = true;
    node.body.visitChildren(this);

    if (_blockDiverges(node.body, allowControlFlow: inControlFlow)) {
      mounted = _tryInvert(newMounted).or(oldMounted);
    }

    inControlFlow = oldInControlFlow;
  }

  @override
  void visitForStatement(ForStatement node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    node.forLoopParts.accept(this);

    final oldInControlFlow = inControlFlow;
    inControlFlow = true;

    node.body.visitChildren(this);

    inControlFlow = oldInControlFlow;
  }

  @override
  void visitBlockFunctionBody(BlockFunctionBody node) {
    final oldMounted = mounted;
    final oldInAsync = inAsync;
    mounted = true.asFact();
    inAsync = node.isAsynchronous;

    node.visitChildren(this);

    mounted = oldMounted;
    inAsync = oldInAsync;
  }

  @override
  void visitTryStatement(TryStatement node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    final oldMounted = mounted;
    node.body.visitChildren(this);
    final afterBody = mounted;
    final beforeCatch =
        mounted == oldMounted ? oldMounted : false.asFact<BinaryExpression>();
    for (final clause in node.catchClauses) {
      mounted = beforeCatch;
      clause.visitChildren(this);
    }

    final finallyBlock = node.finallyBlock;
    if (finallyBlock != null) {
      mounted = beforeCatch;
      finallyBlock.visitChildren(this);
    } else {
      mounted = afterBody;
    }
  }

  @override
  void visitSwitchStatement(SwitchStatement node) {
    if (!inAsync) {
      return node.visitChildren(this);
    }

    node.expression.accept(this);

    final oldInControlFlow = inControlFlow;
    inControlFlow = true;

    final caseInvariant = mounted;
    for (final arm in node.members) {
      arm.visitChildren(this);
      if (mounted != caseInvariant &&
          !_caseDiverges(arm, allowControlFlow: false)) {
        mounted = false.asFact();
      }

      if (_caseDiverges(arm, allowControlFlow: true)) {
        mounted = caseInvariant;
      }
    }

    inControlFlow = oldInControlFlow;
  }
}
