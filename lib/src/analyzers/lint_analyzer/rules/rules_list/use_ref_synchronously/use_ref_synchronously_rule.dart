import 'package:analyzer/dart/ast/ast.dart';
import 'package:analyzer/dart/ast/visitor.dart';
import 'package:analyzer/dart/element/element.dart';
import 'package:analyzer/dart/element/nullability_suffix.dart';
import 'package:analyzer/dart/element/type.dart';
import 'package:collection/collection.dart';

import '../../../../../utils/node_utils.dart';
import '../../../lint_utils.dart';
import '../../../models/internal_resolved_unit_result.dart';
import '../../../models/issue.dart';
import '../../../models/severity.dart';
import '../../models/flutter_rule.dart';
import '../../rule_utils.dart';
import 'async_state_visitor.dart';

part 'visitor.dart';

class UseRefSynchronouslyRule extends FlutterRule {
  static const ruleId = 'use-ref-synchronously';

  UseRefSynchronouslyRule([Map<String, Object> options = const {}])
      : super(
          id: ruleId,
          severity: readSeverity(options, Severity.warning),
          excludes: readExcludes(options),
          includes: readIncludes(options),
        );

  @override
  Iterable<Issue> check(InternalResolvedUnitResult source) {
    final visitor = _Visitor();
    source.unit.accept(visitor);

    return visitor.nodes
        .map((node) => createIssue(
              rule: this,
              location: nodeLocation(node: node, source: source),
              message: "Don't use Ref or WidgetRef across an async gap.",
              verboseMessage: 'Try to move the Ref or WidgetRef usage before '
                  'the async gap. Inside a Widget, you can also check if the '
                  'widget is still mounted before accessing the WidgetRef.',
            ))
        .toList(growable: false);
  }
}
