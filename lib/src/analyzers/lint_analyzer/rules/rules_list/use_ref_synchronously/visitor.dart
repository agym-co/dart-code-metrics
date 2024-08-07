part of 'use_ref_synchronously_rule.dart';

class _Visitor extends RecursiveAstVisitor<void> {
  _Visitor();

  final nodes = <Expression>[];

  void check(Expression node) {
    // Checks each of the statements before `child` for a `mounted` check, and
    // returns whether it did not find one (and the caller should keep looking).

    // Walk back and look for an async gap that is not guarded by a mounted
    // property check.
    AstNode? child = node;
    final asyncStateTracker = AsyncStateTracker();
    while (child != null && child is! FunctionBody) {
      final parent = child.parent;
      if (parent == null) {
        break;
      }

      final asyncState = asyncStateTracker.asyncStateFor(child);
      if (asyncState.isGuarded) {
        return;
      }

      if (asyncState == AsyncState.asynchronous) {
        nodes.add(node);
        return;
      }

      child = parent;
    }

    if (child is FunctionBody) {
      final parent = child.parent;
      if (parent is! FunctionExpression) {
        return;
      }

      var grandparent = parent.parent;
      if (grandparent is NamedExpression) {
        // Given a FunctionBody in a named argument, like
        // `future.catchError(test: (_) {...})`, we step up once more to the
        // argument list.
        grandparent = grandparent.parent;
      }

      if (grandparent is ArgumentList) {
        if (grandparent.parent
            case final InstanceCreationExpression invocation) {
          checkConstructorCallback(invocation, parent, node);
        }

        if (grandparent.parent case final MethodInvocation invocation) {
          checkMethodCallback(invocation, parent, node);
        }
      }
    }
  }

  /// Checks whether [invocation] involves a [callback] argument for a protected
  /// constructor.
  ///
  /// The code inside a callback argument for a protected constructor must not
  /// contain any references to a `BuildContext` without a guarding mounted
  /// check.
  void checkConstructorCallback(
    InstanceCreationExpression invocation,
    FunctionExpression callback,
    Expression errorNode,
  ) {
    final staticType = invocation.staticType;
    if (staticType == null) {
      return;
    }
    final arguments = invocation.argumentList.arguments;
    final positionalArguments =
        arguments.where((a) => a is! NamedExpression).toList();
    final namedArguments = arguments.whereType<NamedExpression>().toList();
    for (final constructor in ProtectedFunction.constructors) {
      if (invocation.constructorName.name?.name == constructor.name &&
          staticType.isSameAs(constructor.type, constructor.library)) {
        checkPositionalArguments(
          constructor.positional,
          positionalArguments,
          callback,
          errorNode,
        );
        checkNamedArguments(
          constructor.named,
          namedArguments,
          callback,
          errorNode,
        );
      }
    }
  }

  /// Checks whether [invocation] involves a [callback] argument for a protected
  /// instance or static method.
  ///
  /// The code inside a callback argument for a protected method must not
  /// contain any references to a `BuildContext` without a guarding mounted
  /// check.
  void checkMethodCallback(
    MethodInvocation invocation,
    FunctionExpression callback,
    Expression errorNode,
  ) {
    final arguments = invocation.argumentList.arguments;
    final positionalArguments =
        arguments.where((a) => a is! NamedExpression).toList();
    final namedArguments = arguments.whereType<NamedExpression>().toList();

    final target = invocation.realTarget;
    final targetElement = target is Identifier ? target.staticElement : null;
    if (targetElement is ClassElement) {
      // Static function called; `target` is the class.
      for (final method in ProtectedFunction.staticMethods) {
        if (invocation.methodName.name == method.name &&
            targetElement.name == method.type) {
          checkPositionalArguments(
            method.positional,
            positionalArguments,
            callback,
            errorNode,
          );
          checkNamedArguments(
            method.named,
            namedArguments,
            callback,
            errorNode,
          );
        }
      }
    } else {
      final staticType = target?.staticType;
      if (staticType == null) {
        return;
      }
      for (final method in ProtectedFunction.instanceMethods) {
        if (invocation.methodName.name == method.name &&
            staticType.element?.name == method.type) {
          checkPositionalArguments(
            method.positional,
            positionalArguments,
            callback,
            errorNode,
          );
          checkNamedArguments(
            method.named,
            namedArguments,
            callback,
            errorNode,
          );
        }
      }
    }
  }

  /// Checks whether [callback] is one of the [namedArguments] for one of the
  /// protected argument [names] for a protected function.
  void checkNamedArguments(
    List<String> names,
    List<NamedExpression> namedArguments,
    Expression callback,
    Expression errorNode,
  ) {
    for (final named in names) {
      final argument =
          namedArguments.firstWhereOrNull((a) => a.name.label.name == named);
      if (argument == null) {
        continue;
      }
      if (callback == argument.expression) {
        nodes.add(errorNode);
      }
    }
  }

  /// Checks whether [callback] is one of the [positionalArguments] for one of
  /// the protected argument [positions] for a protected function.
  void checkPositionalArguments(
    List<int> positions,
    List<Expression> positionalArguments,
    Expression callback,
    Expression errorNode,
  ) {
    for (final position in positions) {
      if (positionalArguments.length > position &&
          callback == positionalArguments[position]) {
        nodes.add(errorNode);
      }
    }
  }

  @override
  void visitClassDeclaration(ClassDeclaration node) {
    if (node.isKeepAliveProvider) return;
    super.visitClassDeclaration(node);
  }

  @override
  void visitFunctionDeclaration(FunctionDeclaration node) {
    if (node.isKeepAliveProvider) return;
    super.visitFunctionDeclaration(node);
  }

  @override
  void visitMethodInvocation(MethodInvocation node) {
    // We don't need to visit both the receiver and method name.
    node.methodName.accept(this);
    node.typeArguments?.accept(this);
    node.argumentList.accept(this);
  }

  @override
  void visitSimpleIdentifier(SimpleIdentifier node) {
    if (_isRefOrRead(node.staticType, skipNullable: true)) {
      check(node);
    }
    super.visitSimpleIdentifier(node);
  }
}

bool _isRefOrRead(DartType? type, {bool skipNullable = false}) {
  if (type is InterfaceType) {
    // `Ref` or `WidgetRef`
    if (skipNullable && type.nullabilitySuffix == NullabilitySuffix.question) {
      return false;
    }

    return _is(
          type,
          Uri.parse('package:flutter_riverpod/src/consumer.dart'),
          'WidgetRef',
        ) ||
        _is(type, Uri.parse('package:riverpod/src/framework/ref.dart'), 'Ref');
  }
  if (type is FunctionType) {
    // `T Function<T>(ProviderListenable<T>)`
    final typeParameter = type.typeFormals.singleOrNull;
    final providerListenableParameter = type.normalParameterTypes.singleOrNull;
    if (typeParameter == null || providerListenableParameter == null) {
      return false;
    }

    return providerListenableParameter is InterfaceType &&
        _is(
          providerListenableParameter,
          Uri.parse('package:riverpod/src/framework/foundation.dart'),
          'ProviderListenable',
        ) &&
        type.namedParameterTypes.isEmpty &&
        type.optionalParameterTypes.isEmpty &&
        type.returnType.element == typeParameter;
  }
  return false;
}

bool _is(InterfaceType type, Uri uri, String name) => [type]
    .followedBy(type.allSupertypes)
    .any((type) => _isExactly(type.element, uri, name));
bool _isExactly(InterfaceElement element, Uri uri, String name) =>
    element.source.uri == uri && element.name == name;

extension on AnnotatedNode {
  bool get isKeepAliveProvider => metadata.any(
        (it) =>
            it.name.staticElement?.source?.uri ==
                Uri.parse(
                  'package:riverpod_annotation/src/riverpod_annotation.dart',
                ) &&
            it.name.name == 'Riverpod' &&
            it.arguments != null &&
            it.arguments!.arguments.any((it) =>
                it is NamedExpression &&
                it.name.label.name == 'keepAlive' &&
                it.expression is BooleanLiteral &&
                (it.expression as BooleanLiteral).value),
      );
}

extension on AsyncState? {
  bool get isGuarded =>
      this == AsyncState.mountedCheck || this == AsyncState.notMountedCheck;
}

extension DartTypeExtension on DartType? {
  /// Returns whether `this` is the same element as [interface], declared in
  /// [library].
  bool isSameAs(String? interface, String? library) {
    final self = this;
    return self is InterfaceType &&
        self.element.name == interface &&
        self.element.library.name == library;
  }
}
